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
  public class ProofEvaluator {
    private string UnderscoreStr = "";
    private static Random random = new Random();

    public static string RandomString(int length) {
      const string chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";
      return new string(Enumerable.Repeat(chars, length)
          .Select(s => s[random.Next(s.Length)]).ToArray());
    }
    public ExpressionFinder expressionFinder = null;
    private List<BitArray> bitArrayList = new List<BitArray>();
    private List<float> executionTimes = new List<float>();
    private List<float> startTimes = new List<float>();
    private Dictionary<int, Result> combinationResults = new Dictionary<int, Result>();
    private DafnyVerifierClient dafnyVerifier;

    private void UpdateCombinationResult(int index) {
      var request = dafnyVerifier.requestsList[index];
      var position = dafnyVerifier.requestToPostConditionPosition[request];
      var lemmaStartPosition = dafnyVerifier.requestToLemmaStartPosition[request];
      var output = dafnyVerifier.dafnyOutput[request];
      var response = output.Response;
      var filePath = output.FileName;
      var startTime = output.StartTime;
      var execTime = output.ExecutionTime;
      executionTimes.Add(execTime);
      startTimes.Add(startTime);
      var expectedOutput =
        $"{filePath}({position},0): Error: A postcondition might not hold on this return path.";
      var expectedInconclusiveOutputStart =
        $"{filePath}({lemmaStartPosition},{validityLemmaNameStartCol}): Verification inconclusive";
      // Console.WriteLine($"{index} => {output}");
      // Console.WriteLine($"{output.EndsWith("0 errors\n")} {output.EndsWith($"resolution/type errors detected in {fileName}.dfy\n")}");
      // Console.WriteLine($"----------------------------------------------------------------");
      var res = DafnyVerifierClient.IsCorrectOutput(response, expectedOutput, expectedInconclusiveOutputStart);
      if (res != Result.IncorrectProof) {
        // correctExpressions.Add(dafnyMainExecutor.processToExpr[p]);
        // Console.WriteLine(output);
        combinationResults[index] = res;
        // Console.WriteLine(p.StartInfo.Arguments);
        Console.WriteLine(Printer.ExprToString(dafnyVerifier.requestToExpr[request]));
      } else if (response.EndsWith("0 errors\n")) {
        combinationResults[index] = Result.FalsePredicate;
      } else if (response.EndsWith($"resolution/type errors detected in {Path.GetFileName(filePath)}\n")) {
        combinationResults[index] = Result.InvalidExpr;
      } else {
        combinationResults[index] = Result.IncorrectProof;
      }
      expressionFinder.combinationResults[index] = combinationResults[index];
    }

    public Dictionary<string, List<string>> GetEqualExpressionList(Expression expr) {
      // The first element of each value's list in the result is the type of list
      Dictionary<string, List<string>> result = new Dictionary<string, List<string>>();
      HoleEvalGraph<string> G = new HoleEvalGraph<string>();
      foreach (var e in Expression.Conjuncts(expr)) {
        if (e is BinaryExpr && (e as BinaryExpr).ResolvedOp == BinaryExpr.ResolvedOpcode.EqCommon) {
          var be = e as BinaryExpr;
          var e0 = Printer.ExprToString(be.E0);
          var e1 = Printer.ExprToString(be.E1);
          if (e0 == e1) {
            continue;
          }
          if (!G.AdjacencyList.ContainsKey(e0)) {
            G.AddVertex(e0);
          }
          if (!G.AdjacencyList.ContainsKey(e1)) {
            G.AddVertex(e1);
          }
          G.AddEdge(new Tuple<string, string>(e0, e1));
        }
      }
      HashSet<string> visited = new HashSet<string>();
      foreach (var e in Expression.Conjuncts(expr)) {
        if (e is BinaryExpr && (e as BinaryExpr).ResolvedOp == BinaryExpr.ResolvedOpcode.EqCommon) {
          var be = e as BinaryExpr;
          var e0 = Printer.ExprToString(be.E0);
          var e1 = Printer.ExprToString(be.E1);
          if (e0 == e1) {
            continue;
          }
          if (visited.Contains(e0) || visited.Contains(e1)) {
            Debug.Assert(visited.Contains(e0));
            Debug.Assert(visited.Contains(e1));
            continue;
          }
          HashSet<string> newVisits = G.DFS(e0);
          visited.UnionWith(newVisits);
          result[e0] = new List<string>();
          // The first element of each value's list in the result is the type of list
          result[e0].Add(be.E0.Type.ToString());
          newVisits.Remove(e0);
          foreach (string s in newVisits) {
            result[e0].Add(s);
          }
        }
      }
      return result;
    }

    public static string GetPrefixedString(string prefix, Expression expr, ModuleDefinition currentModuleDef) {
      using (var wr = new System.IO.StringWriter()) {
        var pr = new Printer(wr);
        pr.Prefix = prefix;
        pr.ModuleForTypes = currentModuleDef;
        pr.PrintExpression(expr, false);
        return wr.ToString();
      }
    }

    public async Task<bool> EvaluateAfterRemoveFileLine(Program program, string removeFileLine, string baseFuncName, int depth) {
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
              return await Evaluate(program, topLevelDecl.FullDafnyName, baseFuncName, depth);
            }
          }
        }
      }
      return false;
    }

    public async Task<bool> Evaluate(Program program, string funcName, string baseFuncName, int depth) {
      if (DafnyOptions.O.HoleEvaluatorServerIpPortList == null) {
        Console.WriteLine("ip port list is not given. Please specify with /holeEvalServerIpPortList");
        return false;
      }
      dafnyVerifier = new DafnyVerifierClient(DafnyOptions.O.HoleEvaluatorServerIpPortList, $"output_{funcName}");
      expressionFinder = new ExpressionFinder(this);
      bool runOnce = DafnyOptions.O.HoleEvaluatorRunOnce;
      int timeLimitMultiplier = 2;
      int timeLimitMultiplierLength = 0;
      while (timeLimitMultiplier >= 1) {
        timeLimitMultiplierLength++;
        timeLimitMultiplier /= 10;
      }
      validityLemmaNameStartCol = 30 + timeLimitMultiplierLength;

      // Collect all paths from baseFunc to func
      Console.WriteLine($"{funcName} {baseFuncName} {depth}");
      if (baseFuncName == null) {
        baseFuncName = funcName;
      }
      Function baseFunc = GetFunction(program, baseFuncName);
      if (baseFunc == null) {
        Console.WriteLine($"couldn't find function {baseFuncName}. List of all functions:");
        foreach (var kvp in program.ModuleSigs) {
          foreach (var topLevelDecl in ModuleDefinition.AllFunctions(kvp.Value.ModuleDef.TopLevelDecls)) {
            Console.WriteLine(topLevelDecl.FullDafnyName);
          }
        }
        return false;
      }
      Function constraintFunc = null;
      if (DafnyOptions.O.HoleEvaluatorConstraint != null) {
        constraintFunc = GetFunction(program, DafnyOptions.O.HoleEvaluatorConstraint);
        if (constraintFunc == null) {
          Console.WriteLine($"constraint function {DafnyOptions.O.HoleEvaluatorConstraint} not found!");
          return false;
        }
      }
      CG = GetCallGraph(baseFunc);
      Function func = GetFunction(program, funcName);
      CurrentPath.Add(new Tuple<Function, FunctionCallExpr, Expression>(baseFunc, null, null));
      GetAllPaths(baseFunc, func);
      if (Paths.Count == 0)
        Paths.Add(new List<Tuple<Function, FunctionCallExpr, Expression>>(CurrentPath));
      // foreach (var p in Paths) {
      //   Console.WriteLine(GetValidityLemma(p));
      //   Console.WriteLine("\n----------------------------------------------------------------\n");
      // }
      // return true;

      UnderscoreStr = RandomString(8);
      dafnyVerifier.sw = Stopwatch.StartNew();
      // Console.WriteLine($"hole evaluation begins for func {funcName}");
      Function desiredFunction = null;
      Function topLevelDeclCopy = null;
      desiredFunction = GetFunction(program, funcName);
      if (desiredFunction != null) {
        // calculate holeEvaluatorConstraint Invocation
        if (constraintFunc != null) {
          Dictionary<string, List<Expression>> typeToExpressionDictForInputs = new Dictionary<string, List<Expression>>();
          foreach (var formal in baseFunc.Formals) {
            var identExpr = Expression.CreateIdentExpr(formal);
            var typeString = formal.Type.ToString();
            if (typeToExpressionDictForInputs.ContainsKey(typeString)) {
              typeToExpressionDictForInputs[typeString].Add(identExpr);
            } else {
              var lst = new List<Expression>();
              lst.Add(identExpr);
              typeToExpressionDictForInputs.Add(typeString, lst);
            }
          }
          var funcCalls = GetAllPossibleFunctionInvocations(program, constraintFunc, typeToExpressionDictForInputs);
          foreach (var funcCall in funcCalls) {
            if (constraintExpr == null) {
              constraintExpr = funcCall;
            } else {
              constraintExpr = Expression.CreateAnd(constraintExpr, funcCall);
            }
          }
          Console.WriteLine($"constraint expr to be added : {Printer.ExprToString(constraintExpr)}");
        }
        expressionFinder.CalcDepthOneAvailableExpresssions(program, desiredFunction);
        topLevelDeclCopy = new Function(
          desiredFunction.tok, desiredFunction.Name, desiredFunction.HasStaticKeyword,
          desiredFunction.IsGhost, desiredFunction.TypeArgs, desiredFunction.Formals,
          desiredFunction.Result, desiredFunction.ResultType, desiredFunction.Req,
          desiredFunction.Reads, desiredFunction.Ens, desiredFunction.Decreases,
          desiredFunction.Body, desiredFunction.ByMethodTok, desiredFunction.ByMethodBody,
          desiredFunction.Attributes, desiredFunction.SignatureEllipsis);
      } else {
        Console.WriteLine($"{funcName} was not found!");
        return false;
      }
      for (int i = 0; i < expressionFinder.availableExpressions.Count; i++) {
        PrintExprAndCreateProcess(program, desiredFunction, expressionFinder.availableExpressions[i], i);
        desiredFunction.Body = topLevelDeclCopy.Body;
      }
      await dafnyVerifier.startAndWaitUntilAllProcessesFinishAndDumpTheirOutputs();
      Console.WriteLine("finish");

      // bool foundCorrectExpr = false;
      for (int i = 0; i < expressionFinder.availableExpressions.Count; i++) {
        UpdateCombinationResult(i);
        // foundCorrectExpr |= combinationResults[i] == Result.CorrectProof;
      }

      // Until here, we only check depth 1 of expressions.
      // Now we try to check next depths
      int numberOfSingleExpr = expressionFinder.availableExpressions.Count;
      for (int dd = 2; dd <= depth; dd++) {
        var prevDepthExprStartIndex = expressionFinder.availableExpressions.Count;
        expressionFinder.CalcNextDepthAvailableExpressions();
        for (int i = prevDepthExprStartIndex; i < expressionFinder.availableExpressions.Count; i++) {
          var expr = expressionFinder.availableExpressions[i];
          PrintExprAndCreateProcess(program, desiredFunction, expr, i);
          desiredFunction.Body = topLevelDeclCopy.Body;
        }
        await dafnyVerifier.startAndWaitUntilAllProcessesFinishAndDumpTheirOutputs();
        for (int i = prevDepthExprStartIndex; i < expressionFinder.availableExpressions.Count; i++) {
          UpdateCombinationResult(i);
        }
      }
      Console.WriteLine($"{dafnyVerifier.sw.ElapsedMilliseconds / 1000}:: finish exploring, try to calculate implies graph");
      int correctProofCount = 0;
      int correctProofByTimeoutCount = 0;
      int incorrectProofCount = 0;
      int invalidExprCount = 0;
      int falsePredicateCount = 0;
      for (int i = 0; i < expressionFinder.availableExpressions.Count; i++) {
        switch (combinationResults[i]) {
          case Result.InvalidExpr: invalidExprCount++; break;
          case Result.FalsePredicate: falsePredicateCount++; break;
          case Result.CorrectProof: correctProofCount++; break;
          case Result.CorrectProofByTimeout: correctProofByTimeoutCount++; break;
          case Result.IncorrectProof: incorrectProofCount++; break;
          case Result.Unknown: throw new NotSupportedException();
        }
      }
      Console.WriteLine("{0,-15} {1,-15} {2,-15} {3,-15} {4, -25} {5, -15}",
        "InvalidExpr", "IncorrectProof", "FalsePredicate", "CorrectProof", "CorrectProofByTimeout", "Total");
      Console.WriteLine("{0,-15} {1,-15} {2,-15} {3,-15} {4, -25} {5, -15}",
        invalidExprCount, incorrectProofCount, falsePredicateCount, correctProofCount, correctProofByTimeoutCount, 
        expressionFinder.availableExpressions.Count);
      string executionTimesSummary = "";
      // executionTimes.Sort();
      for (int i = 0; i < executionTimes.Count; i++) {
        executionTimesSummary += $"{i}, {executionTimes[i].ToString()}\n";
      }
      await File.WriteAllTextAsync($"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}/executionTimeSummary.txt",
            executionTimesSummary);

      string startTimesSummary = "";
      // startTimes.Sort();
      for (int i = 0; i < startTimes.Count; i++) {
        startTimesSummary += $"{i}, {(startTimes[i] - startTimes[0]).ToString()}\n";
      }
      await File.WriteAllTextAsync($"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}/startTimeSummary.txt",
            startTimesSummary);
      // for (int i = 0; i < bitArrayList.Count; i++) {
      //   var ba = bitArrayList[i];
      //   Console.WriteLine("------------------------------");
      //   Console.WriteLine(i + " : " +
      //                     Printer.ExprToString(availableExpressions[i]) + " : " +
      //                     combinationResults[i].ToString());
      //   Console.WriteLine(ToBitString(ba));
      //   Console.WriteLine("------------------------------");
      // }
      // return true;

      // int correctExpressionCount = combinationResults.Count(elem => elem.Value == Result.CorrectProof);
      // if (correctExpressionCount == 0) {
      //   Console.WriteLine("Couldn't find any correct answer. Printing 0 error ones");
      //   for (int i = 0; i < availableExpressions.Count; i++) {
      //     if (combinationResults[i] == Result.InvalidExpr) {
      //       var p = dafnyMainExecutor.dafnyProcesses[i];
      //       Console.WriteLine(p.StartInfo.Arguments);
      //       Console.WriteLine(Printer.ExprToString(dafnyMainExecutor.processToExpr[p]));
      //     }
      //   }
      //   return false;
      // }
      // The 0th process represents no change to the predicate, and
      // if that is a correct predicate, it means the proof already 
      // goes through and no additional conjunction is needed.
      if (combinationResults[0] == Result.CorrectProof || combinationResults[0] == Result.CorrectProofByTimeout) {
        Console.WriteLine("proof already goes through!");
        return true;
      }
      return true;
      Console.WriteLine($"{dafnyVerifier.sw.ElapsedMilliseconds / 1000}:: end");
      return true;
    }

    public void PrintExprAndCreateProcess(Program program, Function func, Expression expr, int cnt) {
      bool runOnce = DafnyOptions.O.HoleEvaluatorRunOnce;
      Console.WriteLine($"{cnt} {Printer.ExprToString(expr)}");
      string lemmaForExprValidityString = GetValidityLemma(Paths[0], null, constraintExpr);

      var funcName = func.FullDafnyName;
      int lemmaForExprValidityPosition = 0;
      int lemmaForExprValidityStartPosition = 0;

      string code = "";
      using (var wr = new System.IO.StringWriter()) {
        var pr = new Printer(wr, DafnyOptions.PrintModes.DllEmbed);
        pr.UniqueStringBeforeUnderscore = UnderscoreStr;
        if (expr.HasCardinality) {
          func.Body = Expression.CreateAnd(expr, func.Body);
        } else {
          func.Body = Expression.CreateAnd(func.Body, expr);
        }
        pr.PrintProgram(program, true);
        code = $"// #{cnt}\n";
        code += $"// {Printer.ExprToString(expr)}\n" + Printer.ToStringWithoutNewline(wr) + "\n\n";
        lemmaForExprValidityStartPosition = code.Count(f => f == '\n') + 1;
        code += lemmaForExprValidityString + "\n";
        lemmaForExprValidityPosition = code.Count(f => f == '\n');
        if (DafnyOptions.O.HoleEvaluatorCreateAuxFiles)
          File.WriteAllTextAsync($"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}{funcName}_{cnt}.dfy", code);
        // Console.WriteLine(Printer.ToStringWithoutNewline(wr));
        // Console.WriteLine("");
      }
      // string dafnyBinaryPath = System.Reflection.Assembly.GetEntryAssembly().Location;
      // dafnyBinaryPath = dafnyBinaryPath.Substring(0, dafnyBinaryPath.Length - 4);
      // The first 22 characters are: "Command Line Options: "
      string env = CommandLineOptions.Clo.Environment.Remove(0, 22);
      var argList = env.Split(' ');
      List<string> args = new List<string>();
      foreach (var arg in argList) {
        if (!arg.EndsWith(".dfy") && !arg.StartsWith("/holeEval") && arg.StartsWith("/")) {
          args.Add(arg);
        }
      }
      // Console.WriteLine($"Creating process : ");
      args.Add("/exitAfterFirstError");
      dafnyVerifier.runDafny(code, args,
          expr, cnt, lemmaForExprValidityPosition, lemmaForExprValidityStartPosition);
      // dafnyMainExecutor.createProcessWithOutput(dafnyBinaryPath,
      //     $"{args} {DafnyOptions.O.HoleEvaluatorWorkingDirectory}{funcName}_{cnt}.dfy " + (runOnce ? "/exitAfterFirstError" : "/proc:Impl*validityCheck*"),
      //     expr, cnt, lemmaForExprValidityPosition, lemmaForExprValidityStartPosition, $"{funcName}_{cnt}");
      // Printer.PrintFunction(transformedFunction, 0, false);
    }
  }
}