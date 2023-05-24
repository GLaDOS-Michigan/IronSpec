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
    private Cloner cloner = new Cloner();
    public static string RandomString(int length) {
      const string chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";
      return new string(Enumerable.Repeat(chars, length)
          .Select(s => s[random.Next(s.Length)]).ToArray());
    }
    public ExpressionFinder expressionFinder = null;
    private List<BitArray> bitArrayList = new List<BitArray>();
    private List<UInt64> executionTimes = new List<UInt64>();
    private Dictionary<int, Result> combinationResults = new Dictionary<int, Result>();
    public DafnyVerifierClient dafnyVerifier;
    private TasksList tasksList = null;
    private Dictionary<string, VerificationTaskArgs> tasksListDictionary = new Dictionary<string, VerificationTaskArgs>();
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
      if (!dafnyVerifier.requestsList.ContainsKey(index)) {
        combinationResults[index] = Result.NoMatchingTrigger;
        return;
      }
      var request = dafnyVerifier.requestsList[index];
      var output = dafnyVerifier.dafnyOutput[request[0]];
      var response = output.Response;
      var filePath = output.FileName;
var execTime = output.ExecutionTimeInMs;
        executionTimes.Add(execTime);
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
        foreach (var stmtExpr in dafnyVerifier.requestToStmtExprList[request[0]]) {
          if (stmtExpr.Expr != null) {
            str += sep + Printer.ExprToString(stmtExpr.Expr);
          } else {
            str += sep + Printer.StatementToString(stmtExpr.Stmt);
          }
          sep = ", ";
        }
        // Console.WriteLine(str);
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

    public class ExprStmtUnion {
      public Statement Stmt;
      public Expression Expr;
      public int Depth;

      public ExprStmtUnion(ExpressionFinder.ExpressionDepth exprDepth) {
        this.Stmt = null;
        this.Expr = exprDepth.expr;
        this.Depth = exprDepth.depth;
      }
      public ExprStmtUnion(ExpressionFinder.StatementDepth stmtDepth) {
        this.Stmt = stmtDepth.stmt;
        this.Expr = null;
        this.Depth = stmtDepth.depth;
      }
    }

    public IEnumerable<List<ExprStmtUnion>> GetExprStmtTuples(List<ExpressionFinder.StatementDepth> availableStatements, 
      List<ExpressionFinder.ExpressionDepth> availableExpressions, int depth) {
      if (depth <= 0) {
        yield break;
      } else if (depth == 1) {
        foreach (var stmt in availableStatements) {
          List<ExprStmtUnion> tuples = new List<ExprStmtUnion>();
          tuples.Add(new ExprStmtUnion(stmt));
          yield return tuples;
        }
        foreach (var expr in availableExpressions) {
          List<ExprStmtUnion> tuples = new List<ExprStmtUnion>();
          tuples.Add(new ExprStmtUnion(expr));
          yield return tuples;
        }
        yield break;
      } else {
        foreach (var t in GetExprStmtTuples(availableStatements, availableExpressions, depth - 1)) {
          {
            List<ExprStmtUnion> tuples = new List<ExprStmtUnion>();
            tuples.AddRange(t);
            yield return tuples;
          }
          foreach (var stmt in availableStatements) 
          {
            if (!t.Contains(new ExprStmtUnion(stmt))) {
              List<ExprStmtUnion> tuples = new List<ExprStmtUnion>();
              tuples.AddRange(t);
              tuples.Add(new ExprStmtUnion(stmt));
              yield return tuples;
            }
          }
          foreach (var expr in availableExpressions) 
          {
            if (!t.Contains(new ExprStmtUnion(expr))) {
              List<ExprStmtUnion> tuples = new List<ExprStmtUnion>();
              tuples.AddRange(t);
              tuples.Add(new ExprStmtUnion(expr));
              yield return tuples;
            }
          }
        }
      }
    }

    public IEnumerable<List<ExprStmtUnion>> GetExpressionTuples(List<ExpressionFinder.ExpressionDepth> availableExpressions, int depth) {
      if (depth <= 0) {
        yield break;
      } else if (depth == 1) {
        foreach (var expr in availableExpressions) {
          List<ExprStmtUnion> tuples = new List<ExprStmtUnion>();
          tuples.Add(new ExprStmtUnion(expr));
          yield return tuples;
        }
        yield break;
      } else {
        foreach (var t in GetExpressionTuples(availableExpressions, depth - 1)) {
          {
            List<ExprStmtUnion> tuples = new List<ExprStmtUnion>();
            tuples.AddRange(t);
            yield return tuples;
          }
          foreach (var expr in availableExpressions) 
          {
            if (!t.Contains(new ExprStmtUnion(expr))) {
              List<ExprStmtUnion> tuples = new List<ExprStmtUnion>();
              tuples.AddRange(t);
              tuples.Add(new ExprStmtUnion(expr));
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
      if (expr == null && trigger != null) {
        return false;
      }
      if (expr != null && trigger == null) {
        return false;
      }
      if (isPredicateName) {
        var exprStrList = Printer.ExprToString(expr).Split('.');
        var exprStr = exprStrList[exprStrList.Length - 1];
        var triggerStr = Printer.ExprToString(trigger);
        return exprStr == triggerStr;
      }
      if (expr.Type.ToString() != trigger.Type.ToString() && trigger.Type.ToString() != "T") {
        return false;
      }
      if (expr is IdentifierExpr) {
        return true;
      } else if (expr is NameSegment) {
        return true;
      } else if (expr is LiteralExpr && trigger is LiteralExpr) {
        var exprLiteral = expr as LiteralExpr;
        var triggerLiteral = trigger as LiteralExpr;
        if (exprLiteral.Type.ToString() == triggerLiteral.Type.ToString())
          return true;
        else
          return false;
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
      } else if (expr is BinaryExpr && trigger is BinaryExpr) {
        var binaryExpr = expr as BinaryExpr;
        var triggerBinaryExpr = trigger as BinaryExpr;
        if (binaryExpr.Op != triggerBinaryExpr.Op) {
          return false;
        }
        if (!IsCompatibleTrigger(binaryExpr.E0, triggerBinaryExpr.E0)) {
          return false;
        }
        if (!IsCompatibleTrigger(binaryExpr.E1, triggerBinaryExpr.E1)) {
          return false;
        }
        return true;
      // } else if (expr is BinaryExpr) {
      //   if (IsCompatibleTrigger((expr as BinaryExpr).E0, trigger)) {
      //     return true;
      //   }
      //   if (IsCompatibleTrigger((expr as BinaryExpr).E1, trigger)) {
      //     return true;
      //   }
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

    public int GetTimeLimitMultiplier(Attributes attributes) {
      if (attributes == null) {
        return 1;
      }
      if (attributes.Name == "timeLimitMultiplier") {
        return Int32.Parse(Printer.ExprToString(attributes.Args[0]));
      }
      return GetTimeLimitMultiplier(attributes.Prev);
    }

    public async Task<bool> EvaluateAfterRemoveFileLine(Program program, string removeFileLine, int depth, int expressionDepth) {
      var erasingLemmaName = CodeModifier.Erase(program, removeFileLine);
      return await Evaluate(program, erasingLemmaName, depth, expressionDepth);
    }

    public async Task<bool> Evaluate(Program program, string lemmaName, int depth, int expressionDepth) {
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

      // Collect all paths from baseFunc to func
      Console.WriteLine($"{lemmaName} {depth} {expressionDepth}");
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
      Console.WriteLine(Printer.StatementToString(baseLemma.Body));
      var filename = includeParser.Normalized(baseLemma.BodyStartTok.filename);
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
        if ((x as QuantifierExpr).SplitQuantifier != null) {
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
      }
      // if (DafnyOptions.O.HoleEvaluatorVerboseMode) {
      //   foreach (var t in typeToTriggerDict.Keys) {
      //     Console.WriteLine("--------------------------------");
      //     Console.WriteLine($"{t} {typeToTriggerDict[t].Count}");
      //     foreach (var trigger in typeToTriggerDict[t]) {
      //       var triggerStr = Printer.ExprToString(trigger);
      //       // numberOfMatches.Add(triggerStr, 0);
      //       Console.WriteLine(triggerStr);
      //     }
      //     Console.WriteLine("--------------------------------");
      //   }
      // }
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
      Dictionary<string, HashSet<ExpressionFinder.ExpressionDepth>> typeToExpressionDict = null;
      if (desiredLemma != null) {
        var expressions = expressionFinder.ListArguments(program, desiredLemma);
        var extendedSeqSelectExpressions = expressionFinder.ExtendSeqSelectExpressions(expressions);
        var extendedFunctionInvocationsExpressions = expressionFinder.ExtendFunctionInvocationExpressions(program, extendedSeqSelectExpressions);
        var extendedExpressions = expressionFinder.ExtendInSeqExpressions(extendedFunctionInvocationsExpressions);
        typeToExpressionDict = expressionFinder.GetRawExpressions(program, desiredLemma, extendedExpressions, true);
      } else {
        Console.WriteLine($"{lemmaName} was not found!");
        return false;
      }

      // if (DafnyOptions.O.HoleEvaluatorVerboseMode) {
      //   Console.WriteLine("Type To Expression Dict:");
      //   foreach (var t in typeToExpressionDict.Keys) {
      //     Console.WriteLine("--------------------------------");
      //     Console.WriteLine($"{t} {typeToExpressionDict[t].Count}");
      //     foreach (var expr in typeToExpressionDict[t]) {
      //       var exprStr = $"{Printer.ExprToString(expr.expr)}:{expr.depth}";
      //       Console.WriteLine(exprStr);
      //     }
      //     Console.WriteLine("--------------------------------");
      //   }
      // }
      // return true;
      var statements = new List<ExpressionFinder.StatementDepth>();
      if (expressionDepth <= 1) {
        var revealFinder = new RevealFinder(this);
        statements.AddRange(revealFinder.GetRevealStatements(program).AsEnumerable());
      }
      var lemmaFinder = new LemmaFinder(this);
      var lemmaStatements = lemmaFinder.GetLemmaStatements(program, typeToExpressionDict, expressionDepth);
      statements.AddRange(lemmaStatements.AsEnumerable());
      var numberOfMatchedExpressions = 0;
      var selectedExpressions = new List<ExpressionFinder.ExpressionDepth>();
      for (int i = 0; i < expressionFinder.availableExpressions.Count; i++) {
        // Console.WriteLine($"{i} {Printer.ExprToString(expressionFinder.availableExpressions[i].expr)}");
        if (expressionFinder.availableExpressions[i].depth != expressionDepth) {
          continue;
        }
        var matchingTrigger = DoesMatchWithAnyTrigger(expressionFinder.availableExpressions[i].expr, typeToTriggerDict);
        if (i == 0 || matchingTrigger != null) {
          if (i != 0) {
            // Console.WriteLine($"{i} {Printer.ExprToString(expressionFinder.availableExpressions[i].expr)} " +
              // $"{expressionFinder.availableExpressions[i].expr.Type.ToString()} " +
              // "\t\t" + Printer.ExprToString(matchingTrigger));
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
      Console.WriteLine($"totalExpressions: {selectedExpressions.Count}");
      Console.WriteLine($"numberOfMatchedExpressions: {numberOfMatchedExpressions}");
      Console.WriteLine($"numberOfRevealAndLemmaStatements: {statements.Count}");
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
      Console.WriteLine($"{dafnyVerifier.sw.ElapsedMilliseconds / 1000}:: start generatinng expressions and lemmas");
      workingLemma = desiredLemma;
      var timeLimitMultiplier = GetTimeLimitMultiplier(desiredLemma.Attributes);
      workingLemmaTimelimitMultiplier = $"{timeLimitMultiplier}m";
      workingLemmaCode = File.ReadAllLines(workingLemma.BodyStartTok.filename);
      mergedCode.Add(String.Join('\n', workingLemmaCode.Take(workingLemma.tok.line - 1)));
      // placeholder for workingLemma
      mergedCode.Add("");
      mergedCode.Add(String.Join('\n', workingLemmaCode.Skip(workingLemma.BodyEndTok.line)));

      PrintExprAndCreateProcess(program, new List<ExprStmtUnion>(), 0);
      int cnt = 1;
      var exprStmtTuples = GetExprStmtTuples(statements, selectedExpressions, depth);
      foreach (var e in exprStmtTuples) {
        PrintExprAndCreateProcess(program, e, cnt);
        // var desiredLemmaBody = desiredLemma.Body.Body;
        // for (int i = 0; i < e.Count; i++) {
        //   desiredLemmaBody.RemoveAt(0);
        // }
        cnt++;
      }
      Console.WriteLine($"{dafnyVerifier.sw.ElapsedMilliseconds / 1000}:: finish generatinng expressions and lemmas");
      await dafnyVerifier.startProofTasksAccordingToPriority();
      for (int i = 0; i < cnt; i++) {
        UpdateCombinationResult(i);
      }
      Console.WriteLine($"{dafnyVerifier.sw.ElapsedMilliseconds / 1000}:: finish exploring");
      dafnyVerifier.Cleanup();
      int correctProofCount = 0;
      int correctProofByTimeoutCount = 0;
      int incorrectProofCount = 0;
      int invalidExprCount = 0;
      int falsePredicateCount = 0;
      int noMatchingTriggerCount = 0;
      int notRunningDueToAlreadyCorrectCodeCount = 0;
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
      Console.WriteLine("{0,-15} {1,-15} {2,-15} {3,-15} {4, -25} {5, -20} {6, -15} {7, -15}",
        "InvalidExpr", "IncorrectProof", "FalsePredicate", "CorrectProof", "CorrectProofByTimeout", "NoMatchingTrigger", "NotRunning", "Total");
      Console.WriteLine("{0,-15} {1,-15} {2,-15} {3,-15} {4, -25} {5, -20} {6, -15} {7, -15}",
        invalidExprCount, incorrectProofCount, falsePredicateCount, correctProofCount, correctProofByTimeoutCount,
        noMatchingTriggerCount, notRunningDueToAlreadyCorrectCodeCount, cnt);
      string executionTimesSummary = "";
      // executionTimes.Sort();
      for (int i = 0; i < executionTimes.Count; i++) {
        executionTimesSummary += $"{i}, {executionTimes[i]}\n";
      }
      await File.WriteAllTextAsync($"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}/executionTimeSummary.txt",
            executionTimesSummary);

      await dafnyVerifier.FinalizeCleanup();
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
        Console.WriteLine(dafnyVerifier.dafnyOutput[dafnyVerifier.requestsList[0][0]].ToString());
        Console.WriteLine("proof already goes through!");
        return true;
      }
      return true;
    }

    private Lemma workingLemma = null;
    private string[] workingLemmaCode;
    private string workingLemmaTimelimitMultiplier = "1m";
    private List<string> mergedCode = new List<string>();

    public void PrintExprAndCreateProcess(Program program, List<ExprStmtUnion> exprStmtList, int cnt) {
      Contract.Requires(workingLemma != null);
      bool runOnce = DafnyOptions.O.HoleEvaluatorRunOnce;
      if (cnt % 5000 == 1) {
        Console.WriteLine($"{dafnyVerifier.sw.ElapsedMilliseconds / 1000}:: {cnt}");
      }
      string signature = $"{cnt} ";
      string sep = "";
      foreach (var exprStmt in exprStmtList) {
        if (exprStmt.Expr != null) {
          signature += sep + $"{Printer.ExprToString(exprStmt.Expr)}:{exprStmt.Depth}";
        } else {
          signature += sep + $"{Printer.StatementToString(exprStmt.Stmt)}:{exprStmt.Depth}";
        }
        sep = ", ";
      }
      // if (DafnyOptions.O.HoleEvaluatorVerboseMode) {
      //   Console.WriteLine(signature);
      // }

      var lemmaName = workingLemma.FullDafnyName;

      var varDeclStmtList = new List<Statement>();
      for (int i = 0; i < exprStmtList.Count; i++) {
        if (exprStmtList[i].Expr != null) {
          List<LocalVariable> localVarList = new List<LocalVariable>();
          List<Expression> lhss = new List<Expression>();
          List<AssignmentRhs> rhss = new List<AssignmentRhs>();
          localVarList.Add(new LocalVariable(workingLemma.tok, workingLemma.tok, $"temp_{cnt}_{i}", new InferredTypeProxy(), true));
          lhss.Add(new IdentifierExpr(workingLemma.tok, $"temp_{cnt}_{i}"));
          rhss.Add(new ExprRhs(exprStmtList[i].Expr));
          UpdateStmt updateStmt = new UpdateStmt(workingLemma.tok, workingLemma.tok, lhss, rhss);
          VarDeclStmt varDeclStmt = new VarDeclStmt(workingLemma.tok, workingLemma.tok, localVarList, updateStmt);
          varDeclStmtList.Add(varDeclStmt);
        }
        else {
          varDeclStmtList.Add(exprStmtList[i].Stmt);
        }
      }

      var changingFilePath = includeParser.Normalized(workingLemma.BodyStartTok.filename);
      // var remoteFolderPath = dafnyVerifier.DuplicateAllFiles(cnt, changingFilePath);

      // add new statements to the beginning of working lemma
      var clonedWorkingLemma = cloner.CloneMethod(workingLemma);
      CodeModifier.InsertIntoBlockStmt((clonedWorkingLemma as Lemma).Body, varDeclStmtList, DafnyOptions.O.ProofEvaluatorInsertionPoint);
      using (var wr = new System.IO.StringWriter()) {
        var pr = new Printer(wr, DafnyOptions.PrintModes.DllEmbed);
        pr.PrintMethod(clonedWorkingLemma, 0, false);
        mergedCode[1] = Printer.ToStringWithoutNewline(wr);
      }
      // mergedCode[1] = Printer
      var newCode = String.Join('\n', mergedCode);
      
      //restore workingLemma to previous state
      // for (int i = 0; i < varDeclStmtList.Count; i++) {
      //   workingLemma.Body.Body.RemoveAt(0);
      // }

      dafnyVerifier.runDafnyProofCheck(newCode, tasksListDictionary[changingFilePath].Arguments.ToList(),
              exprStmtList, cnt, changingFilePath,
              workingLemma.FullDafnyName);
    }
  }
}