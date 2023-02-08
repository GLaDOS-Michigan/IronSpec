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
    private TasksList tasksList = null;
    private Dictionary<string, VerificationTask> tasksListDictionary = new Dictionary<string, VerificationTask>();
    private IncludeParser includeParser = null;

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
      // throw new NotImplementedException("need to rewrite the following based on the changes in dafnyVerifier");
      if (!dafnyVerifier.requestsList.ContainsKey(index)) {
        combinationResults[index] = Result.NoMatchingTrigger;
        return;
      }
      var request = dafnyVerifier.requestsList[index];
      var output = dafnyVerifier.dafnyOutput[request[0]];
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
        var str = "";
        var sep = "";
        foreach (var expr in dafnyVerifier.requestToExprList[request[0]]) {
          str += sep + Printer.ExprToString(expr);
          sep = ", ";
        }
        Console.WriteLine(str);
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
          {
            List<Expression> tuples = new List<Expression>();
            tuples.AddRange(t);
            yield return tuples;
          }
          foreach (var expr in availableExpressions) {
            if (!t.Contains(expr)) {
              List<Expression> tuples = new List<Expression>();
              tuples.AddRange(t);
              tuples.Add(expr);
              yield return tuples;
            }
          }
        }
      }
    }

    public IEnumerable<Expression> GetAllForallExists(Program program) {
      foreach (var kvp in program.ModuleSigs) {
        foreach (var topLevelDecl in ModuleDefinition.AllFunctions(kvp.Value.ModuleDef.TopLevelDecls)) {
          foreach (var e in Expression.Conjuncts(topLevelDecl.Body)) {
            if (e is ForallExpr) {
              yield return e;
            }
            if (e is ExistsExpr) {
              yield return e;
            }
          }
        }
      }
      yield break;
    }

    public IEnumerable<Lemma> GetSubLemmas(Program program, Lemma lemma) {
      List<AttributedExpression> soFarEnsuresExprList = new List<AttributedExpression>();
      foreach (var ens in lemma.Ens) {
        if (ens.E is ApplySuffix) {
          var appSuf = ens.E as ApplySuffix;
          if (!(appSuf.Lhs is NameSegment)) {
            Console.WriteLine($"don't support traversing {Printer.ExprToString(appSuf.Lhs)}");
            continue;
          }
          var ensuresPredicateName = HoleEvaluator.GetFullLemmaNameString(lemma.EnclosingClass.EnclosingModuleDefinition, Printer.ExprToString(appSuf.Lhs));
          var ensuresPredicate = HoleEvaluator.GetFunction(program, ensuresPredicateName);
          if (ensuresPredicate == null) {
            throw new NotSupportedException($"{ensuresPredicateName} not found");
          }

          var argsSubstMap = new Dictionary<IVariable, Expression>();  // maps formal arguments to actuals
          for (int i = 0; i < ensuresPredicate.Formals.Count; i++) {
            argsSubstMap.Add(ensuresPredicate.Formals[i], appSuf.Args[i]);
          }
          var substituter = new AlphaConvertingSubstituter(ensuresPredicate.Body, argsSubstMap, new Dictionary<TypeParameter, Type>());
          var subtitutedNamesExpr = substituter.Substitute(ensuresPredicate.Body);
          Console.WriteLine($"convert \n    {Printer.ExprToString(ensuresPredicate.Body)}\nto\n    {Printer.ExprToString(subtitutedNamesExpr)}");
          foreach (var expr in Expression.Conjuncts(subtitutedNamesExpr)) {
            Lemma subLemma = new Lemma(lemma.tok, lemma.Name, lemma.HasStaticKeyword, lemma.TypeArgs,
                lemma.Ins, lemma.Outs, lemma.Req.ToList(), lemma.Mod, lemma.Ens.ToList(), lemma.Decreases, lemma.Body,
                lemma.Attributes, lemma.SignatureEllipsis);
            subLemma.Req.AddRange(soFarEnsuresExprList);
            subLemma.Ens.Clear();
            subLemma.Ens.Add(new AttributedExpression(expr));
            soFarEnsuresExprList.Add(new AttributedExpression(expr));
            if (expr is ApplySuffix) {
              foreach (var s in GetSubLemmas(program, subLemma)) {
                yield return s;
              }
            }
            yield return subLemma;
            // Console.WriteLine(Printer.ExprToString(expr));
          }
        }
      }
      yield break;
    }

    // public List<Expression> GetTriggers(Expression expr) {
    //   Contract.Requires(expr != null);
    //   Contract.Requires(expr is ForallExpr || expr is ExistsExpr);
    //   var result = new List<Expression>();
    //   if (expr is ForallExpr) {
    //     var forallExpr = expr as ForallExpr;
    //     result.AddRange(forallExppr.Triggers);
    //   }
    //   return result;
    // }

    public bool IsCompatibleTrigger(Expression expr, Expression trigger, bool isPredicateName = false) {
      // Console.WriteLine($"  1 {Printer.ExprToString(expr)} {Printer.ExprToString(trigger)}");
      // Console.WriteLine($"  2 {expr} {trigger}");
      // if (checkType) {
      //   Console.WriteLine($"  3 {expr.Type.ToString()}");
      //   Console.WriteLine($"  4 {trigger.Type.ToString()}");
      // } else {
      //   Console.WriteLine($"  3 checkType = false");
      // }
      if (isPredicateName) {
        var exprStrList = Printer.ExprToString(expr).Split('.');
        var exprStr = exprStrList[exprStrList.Length - 1];
        var triggerStr = Printer.ExprToString(trigger);
        return exprStr == triggerStr;
      }
      if (expr.Type.ToString() != trigger.Type.ToString() && trigger.Type.ToString() != "T") {
        return false;
      }
      if (expr is IdentifierExpr && trigger is IdentifierExpr) {
        return true;
      } else if (trigger is NameSegment) {
        return true;
      } else if (expr is ApplySuffix && trigger is ApplySuffix) {
        var exprSuffix = expr as ApplySuffix;
        var triggerSuffix = trigger as ApplySuffix;
        // Console.WriteLine($"{exprSuffix.Bindings.ArgumentBindings} {triggerSuffix.Bindings.ArgumentBindings}");
        if (exprSuffix.Bindings.ArgumentBindings.Count != triggerSuffix.Bindings.ArgumentBindings.Count) {
          return false;
        }
        for (int i = 0; i < triggerSuffix.Bindings.ArgumentBindings.Count; i++) {
          if (!IsCompatibleTrigger(exprSuffix.Bindings.ArgumentBindings[i].Actual, triggerSuffix.Bindings.ArgumentBindings[i].Actual)) {
            return false;
          }
        }
        if (!IsCompatibleTrigger(exprSuffix.Lhs, triggerSuffix.Lhs, true)) {
          return false;
        }
        return true;
      } else if (expr is ExprDotName && trigger is MemberSelectExpr) {
        var exprDotName = expr as ExprDotName;
        var triggerMemberSelectExpr = trigger as MemberSelectExpr;
        if (!IsCompatibleTrigger(exprDotName.Lhs, triggerMemberSelectExpr.Obj)) {
          return false;
        }
        if (exprDotName.SuffixName != triggerMemberSelectExpr.MemberName) {
          return false;
        }
        return true;
      } else if (expr is SeqSelectExpr && trigger is SeqSelectExpr) {
        var exprSeqSelect = expr as SeqSelectExpr;
        var triggerSeqSelect = trigger as SeqSelectExpr;
        if (exprSeqSelect.SelectOne && triggerSeqSelect.SelectOne) {
          if (!IsCompatibleTrigger(exprSeqSelect.Seq, triggerSeqSelect.Seq)) {
            return false;
          }
          if (!IsCompatibleTrigger(exprSeqSelect.E0, triggerSeqSelect.E0)) {
            return false;
          }
          return true;
        } else if (!exprSeqSelect.SelectOne && !triggerSeqSelect.SelectOne) {
          throw new NotSupportedException();
          return false;
        } else {
          return false;
        }
      }
      return false;
    }

    public Dictionary<string, int> numberOfMatches = new Dictionary<string, int>();
    public Expression DoesMatchWithAnyTrigger(Expression expr, Dictionary<string, List<Expression>> typeToTriggerDict) {
      if (!typeToTriggerDict.ContainsKey(expr.Type.ToString())) {
        return null;
      }
      var triggerList = typeToTriggerDict[expr.Type.ToString()];
      Expression result = null;
      // Console.WriteLine($"DoesMatchWithAny for {Printer.ExprToString(expr)} ---- start");
      foreach (var trigger in triggerList) {
        // if (expr.Type.ToString() == "nat") {
        //   var tmp = IsCompatibleTrigger(expr, trigger);
        // }
        if (IsCompatibleTrigger(expr, trigger)) {
          if (result == null) {
            result = trigger;
          }
          if (DafnyOptions.O.ProofEvaluatorCollectAllTriggerMatches) {
            numberOfMatches[Printer.ExprToString(trigger)]++;
          } else {
            return trigger;
          }
        }
      }
      // Console.WriteLine($"DoesMatchWithAny for {Printer.ExprToString(expr)} ---- end");
      return result;
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
      if (DafnyOptions.O.HoleEvaluatorCommands != null) {
        var input = File.ReadAllText(DafnyOptions.O.HoleEvaluatorCommands);
        tasksList = Google.Protobuf.JsonParser.Default.Parse<TasksList>(input);
        foreach (var task in tasksList.Tasks) {
          tasksListDictionary.Add(task.Path, task);
        }
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

      includeParser = new IncludeParser(program);
      var filename = includeParser.Normalized(baseLemma.BodyStartTok.Filename);
      dafnyVerifier.InitializeBaseFoldersInRemoteServers(program, includeParser.commonPrefix);

      UnderscoreStr = RandomString(8);
      dafnyVerifier.sw = Stopwatch.StartNew();
      // Console.WriteLine($"hole evaluation begins for func {lemmaName}");
      Lemma desiredLemma = null;
      // List<Statement> lemmaBodyBackup = null;
      desiredLemma = ProofEvaluator.GetLemma(program, lemmaName);
      var allForallExists = GetAllForallExists(program);
      Dictionary<string, List<Expression>> typeToTriggerDict = new Dictionary<string, List<Expression>>();
      Dictionary<string, HashSet<string>> typeToTriggerDictHashSet = new Dictionary<string, HashSet<string>>();
      foreach (var x in allForallExists) {
        var trigList = (x as QuantifierExpr).SplitQuantifier;
        // Console.WriteLine(Printer.ExprToString(x));
        foreach (var t in trigList) {
          // Console.WriteLine($"---- {Printer.ExprToString(t)} ----");
          var attributes = (t as ComprehensionExpr).Attributes;
          while (attributes != null) {
            if (attributes.Name == "trigger") {
              foreach (var arg in attributes.Args) {
                if (!typeToTriggerDict.ContainsKey(arg.Type.ToString())) {
                  typeToTriggerDict[arg.Type.ToString()] = new List<Expression>();
                  typeToTriggerDictHashSet[arg.Type.ToString()] = new HashSet<string>();
                }
                if (!typeToTriggerDictHashSet[arg.Type.ToString()].Contains(Printer.ExprToString(arg))) {
                  typeToTriggerDict[arg.Type.ToString()].Add(arg);
                  typeToTriggerDictHashSet[arg.Type.ToString()].Add(Printer.ExprToString(arg));
                }
              }
            }
            attributes = attributes.Prev;
          }
        }
      }
      foreach (var t in typeToTriggerDict.Keys) {
        Console.WriteLine("--------------------------------");
        Console.WriteLine($"{t} {typeToTriggerDict[t].Count}");
        foreach (var trigger in typeToTriggerDict[t]) {
          var triggerStr = Printer.ExprToString(trigger);
          if (DafnyOptions.O.ProofEvaluatorCollectAllTriggerMatches) {
            numberOfMatches.Add(triggerStr, 0);
          }
          Console.WriteLine(triggerStr);
        }
        Console.WriteLine("--------------------------------");
      }
      // var subLemmas = GetSubLemmas(program, desiredLemma);
      // foreach (var subLemma in subLemmas) {
      //   Console.WriteLine("-------");
      //   using (var wr = new System.IO.StringWriter()) {
      //     var pr = new Printer(wr, DafnyOptions.PrintModes.DllEmbed);
      //     pr.PrintMethod(subLemma, 0, false);
      //     Console.WriteLine(Printer.ToStringWithoutNewline(wr));
      //   }
      //   Console.WriteLine("-------");
      // }

      // foreach (var ens in desiredLemma.Ens) {
      //   if (ens.E is ApplySuffix) {
      //     var appSuf = ens.E as ApplySuffix;
      //     var ensuresPredicateName = HoleEvaluator.GetFullLemmaNameString(desiredLemma.EnclosingClass.EnclosingModuleDefinition, Printer.ExprToString(appSuf.Lhs));
      //     var ensuresPredicate = HoleEvaluator.GetFunction(program, ensuresPredicateName);
      //     Console.WriteLine(ensuresPredicate.FullDafnyName);
      //   }
      // }
      // return true;
      Dictionary<string, List<Expression>> typeToExpressionDict = null;
      if (desiredLemma != null) {
        var expressions = expressionFinder.ListArguments(program, desiredLemma);
        var extendedExpressions = expressionFinder.ExtendSeqSelectExpressions(expressions);
        typeToExpressionDict = expressionFinder.GetRawExpressions(program, desiredLemma, expressions, true);
      } else {
        Console.WriteLine($"{lemmaName} was not found!");
        return false;
      }
      // return true;
      var numberOfMatchedExpressions = 0;
      var selectedExpressions = new List<Expression>();
      for (int i = 0; i < expressionFinder.availableExpressions.Count; i++) {
        // Console.WriteLine($"{i} {Printer.ExprToString(expressionFinder.availableExpressions[i])} start");
        var matchingTrigger = DoesMatchWithAnyTrigger(expressionFinder.availableExpressions[i], typeToTriggerDict);
        if (i == 0 || matchingTrigger != null) {
          if (i != 0) {
            Console.WriteLine($"{i} {Printer.ExprToString(expressionFinder.availableExpressions[i])} " +
              $"{expressionFinder.availableExpressions[i].Type.ToString()} " +
              $"{expressionFinder.availableExpressions[i]} " + "\t\t" + Printer.ExprToString(matchingTrigger));
            numberOfMatchedExpressions++;
          }
          selectedExpressions.Add(expressionFinder.availableExpressions[i]);
          // var l = new List<Expression>();
          // l.Add(expressionFinder.availableExpressions[i]);
          // PrintExprAndCreateProcess(program, desiredLemma, l, i);
          // var desiredLemmaBody = desiredLemma.Body.Body;
          // desiredLemmaBody.RemoveAt(0);
        }
      }
      if (DafnyOptions.O.ProofEvaluatorCollectAllTriggerMatches) {
        foreach (var trigger in numberOfMatches) {
          Console.WriteLine($"{trigger.Key}\t{trigger.Value}");
        }
      }
      Console.WriteLine($"totalExpressions: {expressionFinder.availableExpressions.Count}");
      Console.WriteLine($"numberOfMatchedExpressions: {numberOfMatchedExpressions}");
      // return true;
      // await dafnyVerifier.startProofTasksAndWaitUntilAllProcessesFinishAndDumpTheirOutputs();
      // Console.WriteLine("finish");

      // bool foundCorrectExpr = false;
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
      var exprTuples = GetExpressionTuples(selectedExpressions, depth);
      foreach (var e in exprTuples) {
        PrintExprAndCreateProcess(program, desiredLemma, e, cnt);
        // var desiredLemmaBody = desiredLemma.Body.Body;
        // for (int i = 0; i < e.Count; i++) {
        //   desiredLemmaBody.RemoveAt(0);
        // }
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
      int noMatchingTriggerCount = 0;
      for (int i = 0; i < cnt; i++) {
        switch (combinationResults[i]) {
          case Result.InvalidExpr: invalidExprCount++; break;
          case Result.FalsePredicate: falsePredicateCount++; break;
          case Result.CorrectProof: correctProofCount++; break;
          case Result.CorrectProofByTimeout: correctProofByTimeoutCount++; break;
          case Result.IncorrectProof: incorrectProofCount++; break;
          case Result.NoMatchingTrigger: noMatchingTriggerCount++; break;
          case Result.Unknown: throw new NotSupportedException();
        }
      }
      Console.WriteLine("{0,-15} {1,-15} {2,-15} {3,-15} {4, -25} {5, -15} {6, -15}",
        "InvalidExpr", "IncorrectProof", "FalsePredicate", "CorrectProof", "CorrectProofByTimeout", "NoMatchingTrigger", "Total");
      Console.WriteLine("{0,-15} {1,-15} {2,-15} {3,-15} {4, -25} {5, -15} {6, -15}",
        invalidExprCount, incorrectProofCount, falsePredicateCount, correctProofCount, correctProofByTimeoutCount,
        noMatchingTriggerCount, cnt);
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

      var varDeclStmtStringList = new List<string>();
      for (int i = 0; i < exprList.Count; i++) {
        List<LocalVariable> localVarList = new List<LocalVariable>();
        List<Expression> lhss = new List<Expression>();
        List<AssignmentRhs> rhss = new List<AssignmentRhs>();
        localVarList.Add(new LocalVariable(lemma.tok, lemma.tok, $"temp_{cnt}_{i}", new InferredTypeProxy(), true));
        lhss.Add(new IdentifierExpr(lemma.tok, $"temp_{cnt}_${i}"));
        rhss.Add(new ExprRhs(exprList[i]));
        UpdateStmt updateStmt = new UpdateStmt(lemma.tok, lemma.tok, lhss, rhss);
        VarDeclStmt varDeclStmt = new VarDeclStmt(lemma.tok, lemma.tok, localVarList, updateStmt);
        varDeclStmtStringList.Add(Printer.StatementToString(varDeclStmt));
      }

      var changingFilePath = includeParser.Normalized(lemma.BodyStartTok.Filename);
      var remoteFolderPath = dafnyVerifier.DuplicateAllFiles(cnt, changingFilePath);
      var baseCode = File.ReadAllLines(lemma.BodyStartTok.Filename);

      baseCode[lemma.BodyStartTok.line - 1] = baseCode[lemma.BodyStartTok.line - 1].Insert(lemma.BodyStartTok.col, String.Join('\n', varDeclStmtStringList));

      var newCode = String.Join('\n', baseCode);

      dafnyVerifier.runDafnyProofCheck(newCode, tasksListDictionary[changingFilePath].Arguments.ToList(),
              exprList, cnt, $"{remoteFolderPath.Path}/{changingFilePath}",
              lemma.CompileName);
    }
  }
}