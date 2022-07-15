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

    public static Lemma GetLemma(Program program, string lemmaName) {
      foreach (var kvp in program.ModuleSigs) {
        foreach (var d in kvp.Value.ModuleDef.TopLevelDecls) {
          var cl = d as TopLevelDeclWithMembers;
          if (cl != null) {
            foreach (var member in cl.Members) {
              var m = member as Lemma;
              if (m != null) {
                if (m.FullDafnyName == lemmaName) {
                  return m;
                }
              }
            }
          }
        }
      }
      return null;
    }

    private void UpdateCombinationResult(int index) {
      var request = dafnyVerifier.requestsList[index];
      var output = dafnyVerifier.dafnyOutput[request];
      var response = output.Response;
      var filePath = output.FileName;
      var startTime = output.StartTime;
      var execTime = output.ExecutionTime;
      executionTimes.Add(execTime);
      startTimes.Add(startTime);
      // Console.WriteLine($"{index} => {output}");
      // Console.WriteLine($"{output.EndsWith("0 errors\n")} {output.EndsWith($"resolution/type errors detected in {fileName}.dfy\n")}");
      // Console.WriteLine($"----------------------------------------------------------------");
      if (response.EndsWith("0 errors\n")) {
        // correctExpressions.Add(dafnyMainExecutor.processToExpr[p]);
        // Console.WriteLine(output);
        combinationResults[index] = Result.CorrectProof;
        // Console.WriteLine(p.StartInfo.Arguments);
        Console.WriteLine(Printer.ExprToString(dafnyVerifier.requestToExpr[request]));
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

    public IEnumerable<List<Expression>> GetExpressionTuples(List<Expression> availableExpressions, int depth) {
      if (depth <= 0) {
        yield break;
      } else if (depth == 1) {
        foreach (var expr in availableExpressions) {
          List<Expression> tuples = new List<Expression>();
          tuples.Add(expr);
          yield return tuples;
        }
        yield break;
      } else {
        foreach (var t in GetExpressionTuples(availableExpressions, depth - 1)) {
          foreach (var expr in availableExpressions) {
            List<Expression> tuples = new List<Expression>();
            tuples.AddRange(t);
            tuples.Add(expr);
            yield return tuples;
          }
        }
      }
    }

    public async Task<bool> EvaluateAfterRemoveFileLine(Program program, string removeFileLine, int depth) {
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
              return await Evaluate(program, topLevelDecl.FullDafnyName, depth);
            }
          }
        }
      }
      return false;
    }

    public async Task<bool> Evaluate(Program program, string lemmaName, int depth) {
      if (DafnyOptions.O.HoleEvaluatorServerIpPortList == null) {
        Console.WriteLine("ip port list is not given. Please specify with /holeEvalServerIpPortList");
        return false;
      }
      dafnyVerifier = new DafnyVerifierClient(DafnyOptions.O.HoleEvaluatorServerIpPortList, $"output_{lemmaName}");
      expressionFinder = new ExpressionFinder(this);
      bool runOnce = DafnyOptions.O.HoleEvaluatorRunOnce;
      int timeLimitMultiplier = 2;
      int timeLimitMultiplierLength = 0;
      while (timeLimitMultiplier >= 1) {
        timeLimitMultiplierLength++;
        timeLimitMultiplier /= 10;
      }

      // Collect all paths from baseFunc to func
      Console.WriteLine($"{lemmaName} {depth}");
      Lemma baseLemma = ProofEvaluator.GetLemma(program, lemmaName);
      if (baseLemma == null) {
        Console.WriteLine($"couldn't find function {lemmaName}. List of all lemma:");
        foreach (var kvp in program.ModuleSigs) {
          foreach (var d in kvp.Value.ModuleDef.TopLevelDecls) {
            var cl = d as TopLevelDeclWithMembers;
            if (cl != null) {
              foreach (var member in cl.Members) {
                var m = member as Lemma;
                if (m != null) {
                  Console.WriteLine(m.FullDafnyName);
                }
              }
            }
          }
        }
        return false;
      }

      UnderscoreStr = RandomString(8);
      dafnyVerifier.sw = Stopwatch.StartNew();
      // Console.WriteLine($"hole evaluation begins for func {lemmaName}");
      Lemma desiredLemma = null;
      // List<Statement> lemmaBodyBackup = null;
      desiredLemma = ProofEvaluator.GetLemma(program, lemmaName);
      Dictionary<string, List<Expression>> typeToExpressionDict = null;
      if (desiredLemma != null) {
        var expressions = expressionFinder.ListArguments(program, desiredLemma);
        typeToExpressionDict = expressionFinder.GetRawExpressions(program, desiredLemma, expressions, true);
      } else {
        Console.WriteLine($"{lemmaName} was not found!");
        return false;
      }
      // for (int i = 0; i < expressionFinder.availableExpressions.Count; i++) {
      //   PrintExprAndCreateProcess(program, desiredLemma, expressionFinder.availableExpressions[i], i);
      //   var desiredLemmaBody = desiredLemma.Body.Body;
      //   desiredLemmaBody.RemoveAt(0);
      // }
      // await dafnyVerifier.startProofTasksAndWaitUntilAllProcessesFinishAndDumpTheirOutputs();
      // Console.WriteLine("finish");

      // // bool foundCorrectExpr = false;
      // for (int i = 0; i < expressionFinder.availableExpressions.Count; i++) {
      //   UpdateCombinationResult(i);
      //   // foundCorrectExpr |= combinationResults[i] == Result.CorrectProof;
      // }

      // Until here, we only check depth 1 of expressions.
      // Now we try to check next depths
      // int numberOfSingleExpr = expressionFinder.availableExpressions.Count;
      
      // empty expression list should represent the original code without any additions
      PrintExprAndCreateProcess(program, desiredLemma, new List<Expression>(), 0);
      int cnt = 1;
      var exprTuples = GetExpressionTuples(expressionFinder.availableExpressions, depth);
      foreach (var e in exprTuples) {
        PrintExprAndCreateProcess(program, desiredLemma, e, cnt);
        var desiredLemmaBody = desiredLemma.Body.Body;
        for (int i = 0; i < e.Count; i++) {
          desiredLemmaBody.RemoveAt(0);
        }
        cnt++;
      }
      await dafnyVerifier.startProofTasksAndWaitUntilAllProcessesFinishAndDumpTheirOutputs();
      for (int i = 0; i < cnt; i++) {
        UpdateCombinationResult(i);
      }
      Console.WriteLine($"{dafnyVerifier.sw.ElapsedMilliseconds / 1000}:: finish exploring, try to calculate implies graph");
      int correctProofCount = 0;
      int correctProofByTimeoutCount = 0;
      int incorrectProofCount = 0;
      int invalidExprCount = 0;
      int falsePredicateCount = 0;
      for (int i = 0; i < cnt; i++) {
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
    }

    public void PrintExprAndCreateProcess(Program program, Lemma lemma, List<Expression> exprList, int cnt) {
      bool runOnce = DafnyOptions.O.HoleEvaluatorRunOnce;
      string signature = $"{cnt} ";
      string sep = "";
      foreach (var expr in exprList) {
        signature += sep + Printer.ExprToString(expr);
        sep = ", ";
      }
      Console.WriteLine(signature);

      var lemmaName = lemma.FullDafnyName;

      string code = "";
      using (var wr = new System.IO.StringWriter()) {
        var pr = new Printer(wr, DafnyOptions.PrintModes.DllEmbed);
        pr.UniqueStringBeforeUnderscore = UnderscoreStr;
        var methodBody = lemma.Body.Body;
        for (int i = 0; i < exprList.Count; i++) {
          List<LocalVariable> localVarList = new List<LocalVariable>();
          List<Expression> lhss = new List<Expression>();
          List<AssignmentRhs> rhss = new List<AssignmentRhs>();
          localVarList.Add(new LocalVariable(lemma.tok, lemma.tok, $"temp_{cnt}_{i}", new InferredTypeProxy(), true));
          lhss.Add(new IdentifierExpr(lemma.tok, $"temp_{cnt}_${i}"));
          rhss.Add(new ExprRhs(exprList[i]));
          UpdateStmt updateStmt = new UpdateStmt(lemma.tok, lemma.tok, lhss, rhss);
          VarDeclStmt varDeclStmt = new VarDeclStmt(lemma.tok, lemma.tok, localVarList, updateStmt);
          methodBody.Insert(0, varDeclStmt);
        }
        pr.PrintProgram(program, true);
        code = $"// #{cnt}\n";
        code += $"// {signature}\n" + Printer.ToStringWithoutNewline(wr) + "\n\n";
        if (DafnyOptions.O.HoleEvaluatorCreateAuxFiles) {
          File.WriteAllTextAsync($"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}{lemmaName}_{cnt}.dfy", code);
        }
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
        if (!arg.EndsWith(".dfy") && !arg.StartsWith("/holeEval") && !arg.StartsWith("/proofEval") && arg.StartsWith("/")) {
          args.Add(arg);
        }
      }
      // Console.WriteLine($"Creating process : ");
      args.Add("/exitAfterFirstError");
      args.Add("/trace");
      args.Add($"/proc:*{lemma.CompileName}*");
      dafnyVerifier.runDafnyProofCheck(code, args, exprList, cnt);
    }
  }
}