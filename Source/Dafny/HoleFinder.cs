//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------
using System;
using System.Text;
using System.IO;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Diagnostics;
using System.Reflection;
using System.Linq;
using Microsoft.Boogie;
using System.Threading.Tasks;

namespace Microsoft.Dafny {

  public class HoleFinder {
    private string UnderscoreStr = "";
    private static Random random = new Random();
    public static string RandomString(int length) {
      const string chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";
      return new string(Enumerable.Repeat(chars, length)
          .Select(s => s[random.Next(s.Length)]).ToArray());
    }

    private HoleFinderExecutor holeFinderExecutor = new HoleFinderExecutor();

    public HoleFinder() { }

    public void PrintWithFuncFalse(Program program, Function rootFunc, Function func) {
      string funcName;
      if (func.Name == "nullFunc")
        funcName = "NULL";
      else
        funcName = func.FullDafnyName;
      var backupFunc = new Function(func.tok, func.Name, func.HasStaticKeyword,
            func.IsGhost, func.TypeArgs, func.Formals,
            func.Result, func.ResultType, func.Req,
            func.Reads, func.Ens, func.Decreases,
            func.Body, func.ByMethodTok, func.ByMethodBody,
            func.Attributes, func.SignatureEllipsis);
      List<Tuple<Function, FunctionCallExpr, Expression>> p = new List<Tuple<Function, FunctionCallExpr, Expression>>();
      p.Add(new Tuple<Function, FunctionCallExpr, Expression>(rootFunc, null, null));
      string lemmaForExprValidityString = HoleEvaluator.GetValidityLemma(p, null);
      int lemmaForExprValidityPosition = 0;

      using (var wr = new System.IO.StringWriter()) {
        var pr = new Printer(wr, DafnyOptions.PrintModes.DllEmbed);
        pr.UniqueStringBeforeUnderscore = UnderscoreStr;
        if (funcName != "NULL") {
          func.Body = Expression.CreateBoolLiteral(func.Body.tok, false);
        }
        pr.PrintProgram(program, true);
        var code = $"// {funcName} set to false\n" + Printer.ToStringWithoutNewline(wr) + "\n\n";
        code += lemmaForExprValidityString + "\n";
        lemmaForExprValidityPosition = code.Count(f => f == '\n');
        File.WriteAllTextAsync($"/tmp/holeFinder_{funcName}.dfy", code);
      }
      if (funcName != "NULL") {
        func.Body = backupFunc.Body;
      }
      string dafnyBinaryPath = System.Reflection.Assembly.GetEntryAssembly().Location;
      dafnyBinaryPath = dafnyBinaryPath.Substring(0, dafnyBinaryPath.Length - 4);
      string env = CommandLineOptions.Clo.Environment.Remove(0, 22);
      var argList = env.Split(' ');
      string args = "";
      foreach (var arg in argList) {
        if (!arg.EndsWith(".dfy") && !arg.StartsWith("/hole") && arg.StartsWith("/")) {
          args += arg + " ";
        }
      }
      holeFinderExecutor.createProcessWithOutput(dafnyBinaryPath,
          $"{args} /tmp/holeFinder_{funcName}.dfy /exitAfterFirstError",
          func, lemmaForExprValidityPosition, $"holeFinder_{funcName}");
    }

    void PrintCallGraphWithPotentialBugInfo(
        DirectedCallGraph<Function, FunctionCallExpr, Expression> CG, string outputPath) {
      string graphVizOutput = $"digraph \"call_graph\" {{\n";
      graphVizOutput += "\n  node [colorscheme=accent3] # Apply colorscheme to all nodes\n";
      graphVizOutput += "\n  // List of nodes:\n";
      foreach (var node in CG.AdjacencyWeightList.Keys) {
        if (node.Body == null) continue;
        var p = holeFinderExecutor.funcToProcess[node];
        var output = holeFinderExecutor.dafnyOutput[p];
        var fileName = holeFinderExecutor.inputFileName[p];
        var position = holeFinderExecutor.processToPostConditionPosition[p];
        var expectedOutput =
          $"/tmp/{fileName}.dfy({position},0): Error: A postcondition might not hold on this return path.";
        var expectedInconclusiveOutputStart =
          $"/tmp/{fileName}.dfy({position},{HoleEvaluator.validityLemmaNameStartCol}): Verification inconclusive";
        Result result;
        if (DafnyExecutor.IsCorrectOutput(output, expectedOutput, expectedInconclusiveOutputStart)) {
          // correctExpressions.Add(dafnyMainExecutor.processToExpr[p]);
          // Console.WriteLine(output);
          result = Result.CorrectProof;
          // Console.WriteLine(p.StartInfo.Arguments);
          Console.WriteLine(holeFinderExecutor.processToFunc[p].FullDafnyName);
        } else if (output.EndsWith("0 errors\n")) {
          result = Result.FalsePredicate;
        } else if (output.EndsWith($"resolution/type errors detected in {fileName}.dfy\n")) {
          result = Result.InvalidExpr;
        } else {
          result = Result.IncorrectProof;
        }
        switch (result) {
          case Result.CorrectProof:
            graphVizOutput += $"  \"{node.FullDafnyName}\" [label=\"{node.FullDafnyName}\" style=\"filled,dashed\" color=\"black\" fillcolor=1];\n";
            break;
          case Result.FalsePredicate:
            graphVizOutput += $"  \"{node.FullDafnyName}\" [label=\"{node.FullDafnyName}\" style=\"filled,dashed\" color=\"black\" fillcolor=2];\n";
            break;
          case Result.IncorrectProof:
          case Result.InvalidExpr:
            graphVizOutput += $"  \"{node.FullDafnyName}\" [label=\"{node.FullDafnyName}\"];\n";
            break;
        }
      }
      graphVizOutput += "\n  // List of edges:\n";
      foreach (var node in CG.AdjacencyWeightList.Keys) {
        if (node.Body == null) continue;
        foreach (var edge in CG.AdjacencyWeightList[node]) {
          graphVizOutput += $"  \"{node.FullDafnyName}\" -> \"{edge.Item1.FullDafnyName}\";\n";
        }
      }
      graphVizOutput += "}\n";
      File.WriteAllTextAsync(outputPath, graphVizOutput);
    }

    public Function FindHoleAfterRemoveFileLine(Program program, string removeFileLine, string baseFuncName) {
      var fileLineArray = removeFileLine.Split(':');
      var file = fileLineArray[0];
      var line = Int32.Parse(fileLineArray[1]);
      foreach (var kvp in program.ModuleSigs) {
        foreach (var topLevelDecl in ModuleDefinition.AllFunctions(kvp.Value.ModuleDef.TopLevelDecls)) {
          if (Path.GetFileName(topLevelDecl.tok.filename) == file) {
            if (topLevelDecl.BodyStartTok.line <= line && line <= topLevelDecl.BodyEndTok.line) {
              var exprList = Expression.Conjuncts(topLevelDecl.Body).ToList();
              // Console.WriteLine($"topLevelDecl : {topLevelDecl.FullDafnyName}");
              var i = -1;
              for (i = 0; i < exprList.Count - 1; i++) {
                if (exprList[i].tok.line <= line && line < exprList[i + 1].tok.line) {
                  break;
                }
              }
              // Console.WriteLine($"{i} {Printer.ExprToString(exprList[i])}");
              exprList.RemoveAt(i);
              var body = exprList[0];
              for (int j = 1; j < exprList.Count; j++) {
                body = Expression.CreateAnd(body, exprList[j]);
              }
              topLevelDecl.Body = body;
              string dotGraphOutput = $"./callGraph_after_removing_{file}_{line}.dot";
              return FindHole(program, baseFuncName, dotGraphOutput);
            }
          }
        }
      }
      return null;
    }
    public Function FindHole(Program program, string funcName, string dotGraphOutputPath = "") {
      int timeLimitMultiplier = 2;
      int timeLimitMultiplierLength = 0;
      while (timeLimitMultiplier >= 1) {
        timeLimitMultiplierLength++;
        timeLimitMultiplier /= 10;
      }
      HoleEvaluator.validityLemmaNameStartCol = 30 + timeLimitMultiplierLength;
      UnderscoreStr = RandomString(8);
      holeFinderExecutor.sw = Stopwatch.StartNew();
      Function func = HoleEvaluator.GetFunction(program, funcName);
      if (func == null) {
        Console.WriteLine($"couldn't find function {funcName}. List of all functions:");
        foreach (var kvp in program.ModuleSigs) {
          foreach (var topLevelDecl in ModuleDefinition.AllFunctions(kvp.Value.ModuleDef.TopLevelDecls)) {
            Console.WriteLine(topLevelDecl.FullDafnyName);
          }
        }
        return null;
      }
      var CG = HoleEvaluator.GetCallGraph(func);
      Function nullFunc = new Function(
        func.tok, "nullFunc", func.HasStaticKeyword, func.IsGhost,
        func.TypeArgs, func.Formals, func.Result, func.ResultType,
        func.Req, func.Reads, func.Ens, func.Decreases,
        func.Body, func.ByMethodTok, func.ByMethodBody,
        func.Attributes, func.SignatureEllipsis);
      PrintWithFuncFalse(program, func, nullFunc);
      foreach (var kvp in program.ModuleSigs) {
        foreach (var topLevelDecl in ModuleDefinition.AllFunctions(kvp.Value.ModuleDef.TopLevelDecls)) {
          if (topLevelDecl.Body != null && CG.AdjacencyWeightList.ContainsKey(topLevelDecl)) {
            Console.WriteLine(topLevelDecl.FullDafnyName);
            PrintWithFuncFalse(program, func, topLevelDecl);
          }
        }
      }
      holeFinderExecutor.startAndWaitUntilAllProcessesFinishAndDumpTheirOutputs();

      // check if proof already goes through
      var p = holeFinderExecutor.funcToProcess[nullFunc];
      var output = holeFinderExecutor.dafnyOutput[p];
      var fileName = holeFinderExecutor.inputFileName[p];
      var position = holeFinderExecutor.processToPostConditionPosition[p];
      var expectedOutput =
        $"/tmp/{fileName}.dfy({position},0): Error: A postcondition might not hold on this return path.";
      var expectedInconclusiveOutputStart = 
        $"/tmp/{fileName}.dfy({position},{HoleEvaluator.validityLemmaNameStartCol}): Verification inconclusive";
      if (DafnyExecutor.IsCorrectOutput(output, expectedOutput, expectedInconclusiveOutputStart)) {
        Console.WriteLine($"{holeFinderExecutor.sw.ElapsedMilliseconds / 1000}:: proof already goes through!");
        return null;
      }
      if (dotGraphOutputPath == "")
        dotGraphOutputPath = $"./callGraph_{func.Name}.dot";
      PrintCallGraphWithPotentialBugInfo(CG, dotGraphOutputPath);
      Console.WriteLine($"{holeFinderExecutor.sw.ElapsedMilliseconds / 1000}:: finish");
      return null;
    }
  }
}