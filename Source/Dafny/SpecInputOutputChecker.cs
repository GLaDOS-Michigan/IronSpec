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
  public class SpecInputOutputChecker {
    private string UnderscoreStr = "";
    private static Random random = new Random();
    private Cloner cloner = new Cloner();
    public static string RandomString(int length) {
      const string chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";
      return new string(Enumerable.Repeat(chars, length)
          .Select(s => s[random.Next(s.Length)]).ToArray());
    }
    public ExpressionFinder expressionFinder = null;
        // private Cloner cloner = new Cloner();
    private List<BitArray> bitArrayList = new List<BitArray>();
    private List<float> executionTimes = new List<float>();
    private Dictionary<String,float> verboseExecTimes = new Dictionary<string, float>();
    private Dictionary<int,float> verboseExecTimesTotal = new Dictionary<int, float>();
    private List<float> startTimes = new List<float>();
    private ExpressionFinder.ExpressionDepth constraintExpr = null;

    public static bool IsGoodResult(Result result) {
      return (result == Result.CorrectProof ||
              result == Result.CorrectProofByTimeout ||
              result == Result.IncorrectProof ||
              result == Result.Unknown);
    }
    private Dictionary<int, Result> combinationResults = new Dictionary<int, Result>();
    private Dictionary<int, int> negateOfExpressionIndex = new Dictionary<int, int>();
    // private DafnyExecutor dafnyMainExecutor = new DafnyExecutor();
    private DafnyExecutor dafnyImpliesExecutor = new DafnyExecutor();
    public DafnyVerifierClient dafnyVerifier;

    private TasksList tasksList = null;
    private Dictionary<string, VerificationTaskArgs> tasksListDictionary = new Dictionary<string, VerificationTaskArgs>();
    private IncludeParser includeParser = null;
    private List<string> affectedFiles = new List<string>();

    public static int validityLemmaNameStartCol = 0;
    public static string lemmaForExprValidityString = "";
    private static int lemmaForExprValidityLineCount = 0;

    // public static string lemmaForExprValidityString = "";
    // private static int lemmaForExprValidityLineCount = 0;

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

    public static DirectedCallGraph<Function, FunctionCallExpr, Expression> GetCallGraph(Function baseFunc) {
      Contract.Requires(baseFunc != null);
      DirectedCallGraph<Function, FunctionCallExpr, Expression> G = new DirectedCallGraph<Function, FunctionCallExpr, Expression>();
      // Tuple of SubExpression that is going to be parsed, pre-condition to reach this SubExpression, containing Function
      Queue<Tuple<Expression, Expression, Function>> queue = new Queue<Tuple<Expression, Expression, Function>>();
      queue.Enqueue(new Tuple<Expression, Expression, Function>(baseFunc.Body, null, baseFunc));
      G.AddVertex(baseFunc);
      HashSet<string> seenFunctionCalls = new HashSet<string>();
      // keys.Add(Printer.ExprToString(baseF.Body) + ":" + baseF.Body);
      // TODO: Check an example in which a function is called in another function with two different pre-conditions
      while (queue.Count > 0) {
        Tuple<Expression, Expression, Function> currExprCondParentTuple = queue.Dequeue();
        if (currExprCondParentTuple.Item1 == null) continue;
        // Console.WriteLine("Processing " + currExprParentTuple.Item1 + ": " + Printer.ExprToString(currExprParentTuple.Item1));
        if (currExprCondParentTuple.Item1 is FunctionCallExpr /*&& (currExpr as FunctionCallExpr).Function.Body != null*/) {
          // if (!keys.Contains(Printer.ExprToString((currExprParentTuple.Item1 as FunctionCallExpr).Function.Body) + ":" + (currExprParentTuple.Item1 as FunctionCallExpr).Function.Body)) {
          // Console.WriteLine("Adding " + (currExprParentTuple.Item1 as FunctionCallExpr).Function.Body + ": " + Printer.ExprToString((currExprParentTuple.Item1 as FunctionCallExpr).Function.Body));
          var funcCallCondAsString = $"{currExprCondParentTuple.Item3.Name} -> " +
                                     $"{(currExprCondParentTuple.Item1 as FunctionCallExpr).Function.Name} -> ";
          if (currExprCondParentTuple.Item2 != null) {
            funcCallCondAsString += $"{Printer.ExprToString(currExprCondParentTuple.Item2)}";
          } else {
            funcCallCondAsString += "NULL";
          }
          if (!seenFunctionCalls.Contains(funcCallCondAsString)) {
            seenFunctionCalls.Add(funcCallCondAsString);
            // if (currExprCondParentTuple.Item2 != null) {
            //   Console.WriteLine($"condition : {Printer.ExprToString(currExprCondParentTuple.Item2)}");
            // } else {
            //   Console.WriteLine($"condition : null");
            // }
            // if ((currExprCondParentTuple.Item1 as FunctionCallExpr).Function.ToString() == ) {

            // }
            if (currExprCondParentTuple.Item3 != (currExprCondParentTuple.Item1 as FunctionCallExpr).Function) {
              // Console.WriteLine("Here => "+ Printer.ExprToString((currExprCondParentTuple.Item1 as FunctionCallExpr).Function.Body));
              queue.Enqueue(new Tuple<Expression, Expression, Function>(
                (currExprCondParentTuple.Item1 as FunctionCallExpr).Function.Body,
                null,
                (currExprCondParentTuple.Item1 as FunctionCallExpr).Function));
              G.AddVertex((currExprCondParentTuple.Item1 as FunctionCallExpr).Function);
              G.AddEdge(
                currExprCondParentTuple.Item3,
                (currExprCondParentTuple.Item1 as FunctionCallExpr).Function,
                currExprCondParentTuple.Item1 as FunctionCallExpr,
                currExprCondParentTuple.Item2);
              // Console.WriteLine("-------------------------------------");
              // keys.Add(Printer.ExprToString((currExprParentTuple.Item1 as FunctionCallExpr).Function.Body) + ":" + (currExprParentTuple.Item1 as FunctionCallExpr).Function.Body);
            }
          }
        }
        if (currExprCondParentTuple.Item1 is ITEExpr) {
          // Console.WriteLine($"ite expr here: {Printer.ExprToString(currExprCondParentTuple.Item1)}");
          var iteExpr = currExprCondParentTuple.Item1 as ITEExpr;

          // add Condition
          queue.Enqueue(new Tuple<Expression, Expression, Function>(
            iteExpr.Test, currExprCondParentTuple.Item2, currExprCondParentTuple.Item3));

          // add then path
          	          Expression thenCond;
          if (currExprCondParentTuple.Item2 != null && currExprCondParentTuple.Item2 is LetExpr) {
            var prevLet = currExprCondParentTuple.Item2 as LetExpr;
            thenCond = Expression.CreateLet(prevLet.tok, prevLet.LHSs, prevLet.RHSs, 
              Expression.CreateAnd(prevLet.Body, iteExpr.Test), prevLet.Exact);
          }
          else {
            thenCond = currExprCondParentTuple.Item2 != null ?
              Expression.CreateAnd(currExprCondParentTuple.Item2, iteExpr.Test) :
              iteExpr.Test;
          }
          queue.Enqueue(new Tuple<Expression, Expression, Function>(
            iteExpr.Thn, thenCond, currExprCondParentTuple.Item3));
          // add else path
          Expression elseCond;
          if (currExprCondParentTuple.Item2 != null && currExprCondParentTuple.Item2 is LetExpr) {
            var prevLet = currExprCondParentTuple.Item2 as LetExpr;
            elseCond = Expression.CreateLet(prevLet.tok, prevLet.LHSs, prevLet.RHSs, 
              Expression.CreateAnd(prevLet.Body, 
                Expression.CreateNot(iteExpr.Test.tok, iteExpr.Test)
              ), prevLet.Exact);
          }
          else {
            elseCond = currExprCondParentTuple.Item2 != null ?
              Expression.CreateAnd(currExprCondParentTuple.Item2,
                                   Expression.CreateNot(iteExpr.Test.tok, iteExpr.Test)) :
              Expression.CreateNot(iteExpr.Test.tok, iteExpr.Test);
          }
          queue.Enqueue(new Tuple<Expression, Expression, Function>(
            iteExpr.Els, elseCond, currExprCondParentTuple.Item3));

          G.AddVertex(currExprCondParentTuple.Item3);
        } else if (currExprCondParentTuple.Item1 is MatchExpr) {
          var matchExpr = currExprCondParentTuple.Item1 as MatchExpr;
          // add source
          queue.Enqueue(new Tuple<Expression, Expression, Function>(
            matchExpr.Source, currExprCondParentTuple.Item2, currExprCondParentTuple.Item3));

          // add cases
          // Console.WriteLine(Printer.ExprToString(matchExpr));
          foreach (var c in matchExpr.Cases) {
            // Console.WriteLine($"{c.Ctor} -> {c.Ctor.Name}");
            Expression cond;
            if (currExprCondParentTuple.Item2 != null && currExprCondParentTuple.Item2 is LetExpr) {
              var prevLet = currExprCondParentTuple.Item2 as LetExpr;
              cond = new LetExpr(prevLet.tok, prevLet.LHSs, prevLet.RHSs, 
                Expression.CreateAnd(prevLet.Body, new MemberSelectExpr(c.Ctor.tok, matchExpr.Source, c.Ctor.Name)), prevLet.Exact);
            }
            else {
              cond = currExprCondParentTuple.Item2 != null ?
                Expression.CreateAnd(currExprCondParentTuple.Item2, new MemberSelectExpr(c.Ctor.tok, matchExpr.Source, c.Ctor.Name)) :
                new MemberSelectExpr(c.Ctor.tok, matchExpr.Source, c.Ctor.Name + "?");
          }
            queue.Enqueue(new Tuple<Expression, Expression, Function>(
              c.Body, cond, currExprCondParentTuple.Item3));
          }
          G.AddVertex(currExprCondParentTuple.Item3);
          // Console.WriteLine("----------------------------------------------------------------");
        } else if (currExprCondParentTuple.Item1 is ExistsExpr) {
          var existsExpr = currExprCondParentTuple.Item1 as ExistsExpr;
          var lhss = new List<CasePattern<BoundVar>>();
          var rhss = new List<Expression>();
          foreach (var bv in existsExpr.BoundVars) {
            lhss.Add(new CasePattern<BoundVar>(bv.Tok,
              new BoundVar(bv.Tok, bv.Name, bv.Type)));
          }
          rhss.Add(existsExpr.Term);
        Expression prevCond;
          if (currExprCondParentTuple.Item2 != null && currExprCondParentTuple.Item2 is LetExpr) {
            var prevLet = currExprCondParentTuple.Item2 as LetExpr;
            prevCond = Expression.CreateLet(prevLet.tok, prevLet.LHSs, prevLet.RHSs, 
              Expression.CreateAnd(prevLet.Body, existsExpr), prevLet.Exact);
          }
          else {
            prevCond = currExprCondParentTuple.Item2 != null ?
              Expression.CreateAnd(currExprCondParentTuple.Item2, existsExpr) :
              existsExpr;
          }
          var cond = Expression.CreateAnd(prevCond, Expression.CreateLet(existsExpr.BodyStartTok, lhss, rhss,
            Expression.CreateBoolLiteral(existsExpr.BodyStartTok, true), false));

          queue.Enqueue(new Tuple<Expression, Expression, Function>(existsExpr.Term, cond, currExprCondParentTuple.Item3));
          G.AddVertex(currExprCondParentTuple.Item3);
        }
        else if (currExprCondParentTuple.Item1 is LetExpr) {
          var letExpr = currExprCondParentTuple.Item1 as LetExpr;
          var currLetExpr = letExpr;
          var lhss = new List<CasePattern<BoundVar>>();
          var rhss = new List<Expression>();
          while (true) {
            for (int i = 0; i < currLetExpr.LHSs.Count; i++) {
              var lhs = currLetExpr.LHSs[i];
              var rhs = currLetExpr.RHSs[0];
              // lhss.Add(new CasePattern<BoundVar>(bv.Tok,
              //   new BoundVar(bv.Tok, currExprCondParentTuple.Item3.Name + "_" + bv.Name, bv.Type)));
              lhss.Add(new CasePattern<BoundVar>(lhs.tok,
                new BoundVar(lhs.tok, lhs.Id, lhs.Expr != null ? lhs.Expr.Type : lhs.Var.Type)));
              rhss.Add(rhs);
            }
            if (currLetExpr.Body is LetExpr) {
              currLetExpr = currLetExpr.Body as LetExpr;
            }
            else {
              break;
            }
          }
          // var cond = currExprCondParentTuple.Item2 != null ?
          //   Expression.CreateAnd(currExprCondParentTuple.Item2, letExpr) :
          //   letExpr;
          var cond = Expression.CreateLet(letExpr.Body.tok, lhss, rhss,
            Expression.CreateBoolLiteral(letExpr.BodyStartTok, true), letExpr.Exact);
          queue.Enqueue(new Tuple<Expression, Expression, Function>(letExpr.Body, cond, currExprCondParentTuple.Item3));
          G.AddVertex(currExprCondParentTuple.Item3);
        }
        else if(currExprCondParentTuple.Item1 is ForallExpr) {
          var forallExpr = currExprCondParentTuple.Item1 as ForallExpr;
          var lhss = new List<CasePattern<BoundVar>>();
          var rhss = new List<Expression>();
           foreach (var bv in forallExpr.BoundVars) {
            lhss.Add(new CasePattern<BoundVar>(bv.Tok,
              new BoundVar(bv.Tok, bv.Name, bv.Type)));
          }
          // rhss.Add(forallExpr.Term);
          if(forallExpr.Range == null){
            rhss.Add(Expression.CreateBoolLiteral(forallExpr.BodyStartTok, true));
          }else{
            rhss.Add(forallExpr.Range);
          }
           var prevCond= currExprCondParentTuple.Item2 != null ?
            Expression.CreateAnd(currExprCondParentTuple.Item2, forallExpr) :
            forallExpr;
           var cond = Expression.CreateAnd(prevCond, Expression.CreateLet(forallExpr.BodyStartTok, lhss, rhss,
            forallExpr.Term, false));
          queue.Enqueue(new Tuple<Expression, Expression, Function>(forallExpr.Term, cond, currExprCondParentTuple.Item3));
          G.AddVertex(currExprCondParentTuple.Item3);
        } else {
          foreach (var e in currExprCondParentTuple.Item1.SubExpressions) {
            // if (!keys.Contains(Printer.ExprToString(e) + ":" + e)) {
            // Console.WriteLine("Adding " + e + ": " + Printer.ExprToString(e));
            // if (e is MatchExpr) {
            //   // Console.WriteLine($"MatchExpr : {Printer.ExprToString(e)}");
            //   queue.Enqueue(new Tuple<Expression, Expression, Function>(e, e, currExprCondParentTuple.Item3));
            //   G.AddVertex(currExprCondParentTuple.Item3);
            // } else if (e is ITEExpr) {
            //   // Console.WriteLine($"ITEExpr : {Printer.ExprToString(e)}");
            //   queue.Enqueue(new Tuple<Expression, Expression, Function>(e, e, currExprCondParentTuple.Item3));
            //   G.AddVertex(currExprCondParentTuple.Item3);
            // } else {
            // Console.WriteLine($"else : {e} -> {Printer.ExprToString(e)}");
            queue.Enqueue(new Tuple<Expression, Expression, Function>(e, currExprCondParentTuple.Item2, currExprCondParentTuple.Item3));
            G.AddVertex(currExprCondParentTuple.Item3);
            // }
          }
        }
      }
      return G;
    }

    DirectedCallGraph<Function, FunctionCallExpr, Expression> CG;
    List<List<Tuple<Function, FunctionCallExpr, Expression>>> Paths =
      new List<List<Tuple<Function, FunctionCallExpr, Expression>>>();
    List<Tuple<Function, FunctionCallExpr, Expression>> CurrentPath =
      new List<Tuple<Function, FunctionCallExpr, Expression>>();

    List<List<Tuple<Function, FunctionCallExpr, Expression>>> MutationsPaths =
      new List<List<Tuple<Function, FunctionCallExpr, Expression>>>();
    DirectedCallGraph<Function, FunctionCallExpr, Expression> MCG;
      List<Tuple<Function, FunctionCallExpr, Expression>> CurrentPathMutations =
      new List<Tuple<Function, FunctionCallExpr, Expression>>();

    public void GetAllPaths(Function source, Function destination) {
      if (source.FullDafnyName == destination.FullDafnyName) {
        Paths.Add(new List<Tuple<Function, FunctionCallExpr, Expression>>(CurrentPath));
        return;
      }
      foreach (var nwPair in CG.AdjacencyWeightList[source]) {
        CurrentPath.Add(new Tuple<Function, FunctionCallExpr, Expression>(
          nwPair.Item1, nwPair.Item2, nwPair.Item3));
        GetAllPaths(nwPair.Item1, destination);
        CurrentPath.RemoveAt(CurrentPath.Count - 1);
      }
    }

    public void GetAllMutationsPaths(Function source, Function destination) {
      if (source.FullDafnyName == destination.FullDafnyName) {
        MutationsPaths.Add(new List<Tuple<Function, FunctionCallExpr, Expression>>(CurrentPathMutations));
        return;
      }
      foreach (var nwPair in MCG.AdjacencyWeightList[source]) {
        CurrentPathMutations.Add(new Tuple<Function, FunctionCallExpr, Expression>(
          nwPair.Item1, nwPair.Item2, nwPair.Item3));
        GetAllMutationsPaths(nwPair.Item1, destination);
        CurrentPathMutations.RemoveAt(CurrentPathMutations.Count - 1);
      }
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
    public static string GetNonPrefixedString(Expression expr, ModuleDefinition currentModuleDef) {
      using (var wr = new System.IO.StringWriter()) {
        var pr = new Printer(wr);
        pr.ModuleForTypes = currentModuleDef;
        pr.PrintExpression(expr, false);
        return wr.ToString();
      }
    }

public static int[] AllIndexesOf(string str, string substr, bool ignoreCase = false)
{
    if (string.IsNullOrWhiteSpace(str) ||
        string.IsNullOrWhiteSpace(substr))
    {
        throw new ArgumentException("String or substring is not specified.");
    }

    var indexes = new List<int>();
    int index = 0;

    while ((index = str.IndexOf(substr, index, ignoreCase ? StringComparison.OrdinalIgnoreCase : StringComparison.Ordinal)) != -1)
    {
        indexes.Add(index++);
    }

    return indexes.ToArray();
}

    public void PrintAllLemmas(Program program, string lemmaName) {
      foreach (var kvp in program.ModuleSigs) {
        foreach (var d in kvp.Value.ModuleDef.TopLevelDecls) {
          var cl = d as TopLevelDeclWithMembers;
          if (cl != null) {
            foreach (var member in cl.Members) {
              var m = member as Lemma;
              if (m != null) {
                Console.WriteLine("LEMMA NAME = " + m.FullDafnyName);
              }
            }
          }
        }
      }
    }
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

    public static Method GetMethod(Program program, string methodName) {
      foreach (var kvp in program.ModuleSigs) {
        foreach (var d in kvp.Value.ModuleDef.TopLevelDecls) {
          var cl = d as TopLevelDeclWithMembers;
          if (cl != null) {
            foreach (var member in cl.Members) {
              var m = member as Method;
              if (m != null) {
                if (m.FullDafnyName == methodName) {
                  return m;
                }
              }
            }
          }
        }
      }
      return null;
    }

        public void PrintAllMethods(Program program, string methodName) {
      foreach (var kvp in program.ModuleSigs) {
        foreach (var d in kvp.Value.ModuleDef.TopLevelDecls) {
          var cl = d as TopLevelDeclWithMembers;
          if (cl != null) {
            foreach (var member in cl.Members) {
              var m = member as Method;
              if (m != null) {
                Console.WriteLine("Method NAME = " + m.FullDafnyName);
              }
            }
          }
        }
      }
    }


    public async Task<bool> EvaluateInputOutputCheck(Program program, Program unresolvedProgram, string funcName, string lemmaName, string proofModuleName, string baseFuncName, int depth, bool mutationsFromParams,Program proofProg, Program unresolvedProofProgram) {
      if (DafnyOptions.O.HoleEvaluatorServerIpPortList == null) {
        Console.WriteLine("ip port list is not given. Please specify with /holeEvalServerIpPortList");
        return false;
      }
      // Collect all paths from baseFunc to func
      Console.WriteLine($"{funcName} {baseFuncName} {depth}");
      if (baseFuncName == null) {
        baseFuncName = funcName;
      }
      Function baseFunc = null;
      if(proofProg != null){
       baseFunc = GetFunction(proofProg, baseFuncName);
      }else{
       baseFunc = GetFunction(program, baseFuncName);
      }

      if (baseFunc == null) {
        Console.WriteLine($"couldn't find function {baseFuncName}. List of all functions:");
        foreach (var kvp in program.ModuleSigs) {
          foreach (var topLevelDecl in ModuleDefinition.AllFunctions(kvp.Value.ModuleDef.TopLevelDecls)) {
            Console.WriteLine(topLevelDecl.FullDafnyName);
          }
        }
        return false;
      }
      CG = GetCallGraph(baseFunc);
      Function func = GetFunction(program, funcName);
      Function mutationRootFunc = GetFunction(program, DafnyOptions.O.MutationRootName);
      CurrentPath.Add(new Tuple<Function, FunctionCallExpr, Expression>(baseFunc, null, null));
      GetAllPaths(baseFunc, func);
      if(mutationRootFunc == null)
      {
         Console.WriteLine("mutationRootFunc is null");
        return false;
      }
      MCG = GetCallGraph(mutationRootFunc);
      CurrentPathMutations.Add(new Tuple<Function, FunctionCallExpr, Expression>(mutationRootFunc, null, null));
      GetAllMutationsPaths(mutationRootFunc,func);
      if (Paths.Count == 0)
        Paths.Add(new List<Tuple<Function, FunctionCallExpr, Expression>>(CurrentPath));


      UnderscoreStr = RandomString(8);
      // dafnyVerifier.sw = Stopwatch.StartNew();
      Console.WriteLine($"hole evaluation begins for func {funcName}");
      Function desiredFunction = null;
      Function desiredFunctionUnresolved = null;
      Function desiredFunctionMutationRoot = null;
      Function topLevelDeclCopy = null;
      Method desiredMethod = null;
      Method desiredMethodUnresolved = null;
      desiredFunction = GetFunction(program, funcName);



      if (desiredFunction != null) {
        includeParser = new IncludeParser(program);
        var filename = "";
        if(desiredFunction.BodyStartTok.Filename == null)
        {
          filename = includeParser.Normalized(program.FullName);
        }else{
          filename = includeParser.Normalized(desiredFunction.BodyStartTok.Filename);
        }
        foreach (var file in includeParser.GetListOfAffectedFilesBy(filename)) {
          affectedFiles.Add(file);
          affectedFiles = affectedFiles.Distinct().ToList();
        }

      if(proofProg != null){
        // dafnyVerifier.InitializeBaseFoldersInRemoteServers(proofProg, includeParser.commonPrefix);
        affectedFiles.Add(filename);
        affectedFiles = affectedFiles.Distinct().ToList();
        desiredMethod = GetMethod(proofProg, lemmaName);
        Lemma desiredLemmm = GetLemma(proofProg, lemmaName);
      if (desiredLemmm == null && desiredMethod == null) {
        Console.WriteLine($"couldn't find function {desiredLemmm}. List of all lemmas:");
        PrintAllLemmas(proofProg, lemmaName);
        Console.WriteLine($"couldn't find function {desiredMethod}. List of all methods:");
        PrintAllMethods(proofProg, lemmaName);
        return false;
      }

        includeParser = new IncludeParser(proofProg);

      }else{
        // dafnyVerifier.InitializeBaseFoldersInRemoteServers(program, includeParser.commonPrefix);
        affectedFiles.Add(filename);
        affectedFiles = affectedFiles.Distinct().ToList();
      }


        // expressionFinder.CalcDepthOneAvailableExpresssionsFromFunction(program, desiredFunction);
        desiredFunctionUnresolved = GetFunctionFromUnresolved(unresolvedProgram, funcName);
        desiredFunctionMutationRoot = GetFunctionFromUnresolved(unresolvedProgram,DafnyOptions.O.MutationRootName);
        desiredMethodUnresolved = GetMethodFromUnresolved(unresolvedProgram,lemmaName);
        if (DafnyOptions.O.HoleEvaluatorRemoveFileLine != null) {
          var fileLineList = DafnyOptions.O.HoleEvaluatorRemoveFileLine.Split(',');
          foreach (var fileLineString in fileLineList) {
            var fileLineArray = fileLineString.Split(':');
            var file = fileLineArray[0];
            var line = Int32.Parse(fileLineArray[1]);
            CodeModifier.EraseFromPredicate(desiredFunctionUnresolved as Predicate, line);
          }
        }
        Contract.Assert(desiredFunctionUnresolved != null);
      
      } else {
        Console.WriteLine($"{funcName} was not found!");
        return false;
      }

      DafnyOptions.O.HoleEvaluatorExpressionDepth = 10;
      // lets check 
      bool simpleCheck = true;
      expressionFinder = new ExpressionFinder(this);
      //simple check
      if(desiredMethod is Lemma) //TODO
      {

      }else{
            Console.WriteLine("\n---Start Simple Check Ens---\n");

        foreach(var inputF in desiredMethod.Ins)
        {
          // var test = expressionFinder.TraverseFormalSimplified(proofProg,new ExpressionFinder.ExpressionDepth(Expression.CreateIdentExpr(inputF),1)).ToList();
          simpleCheck &= simpleEnsSanityCheck(desiredMethod,inputF,false);
        }
        foreach(var outF in desiredMethod.Outs)
        {
          simpleCheck &= simpleEnsSanityCheck(desiredMethod,outF,true);
        } 

      }
    Console.WriteLine("\nSimpleCheck Ens PASS = " + simpleCheck);
// end simple check
// simple check req 
  Console.WriteLine("\n---Start Simple Check Req---\n");
  simpleCheck = true;
  foreach(var inputF in desiredMethod.Ins)
    {
      // var test = expressionFinder.TraverseFormalSimplified(proofProg,new ExpressionFinder.ExpressionDepth(Expression.CreateIdentExpr(inputF),1)).ToList();
      simpleCheck &= simpleReqSanityCheck(desiredMethod,inputF,false);
    }
  foreach(var outF in desiredMethod.Outs)
    {
      simpleCheck &= simpleReqSanityCheck(desiredMethod,outF,true);
    } 
     Console.WriteLine("SimpleCheck Req PASS = " + simpleCheck);
        
// start deeper check
    Console.WriteLine("\n--- Start Full Check For Ensures ---\n");
         var deepCheck = true;
         var noInputIsNeededInOutput = false;
  Console.WriteLine("Sanity Checking Parameters:\n");

    foreach(var inputF in desiredMethod.Ins)
        {
          var test = expressionFinder.TraverseFormalSimplified(proofProg,new ExpressionFinder.ExpressionDepth(Expression.CreateIdentExpr(inputF),1)).ToList();
          // de-duplicate/turn traverseFormalToFormal
          Dictionary<string,Formal> tfs = new Dictionary<string,Formal>();
          foreach (var extendedF in test)
          {
            var name = Printer.ExprToString(extendedF.expr);
            Formal f = new Formal(extendedF.expr.tok,name,extendedF.expr.Type,true,true,extendedF.expr);
            if(!(tfs.ContainsKey(name)))
            {
              tfs.Add(name,f);
            }
            
          }
          // gathered nested formals
          foreach (var nestedF in tfs.Values)
          {
            var sanCheck = simpleEnsSanityCheck(desiredMethod,nestedF,false);
             deepCheck &= sanCheck;
             noInputIsNeededInOutput |= sanCheck;
          }

        }
        if(!noInputIsNeededInOutput && desiredMethod.Ins.Count > 0){
            Console.WriteLine("\n-- FLAG(HIGH) -- : NONE of Ensures depend on Any input parameters \n");
          }
        Console.WriteLine("All parameters Pass Sanity Check? = " + deepCheck + "\n");
        Console.WriteLine("Sanity Checking OutPuts:\n");
        foreach(var outF in desiredMethod.Outs)
        {
          deepCheck = true;
          bool notMentionedAtAll = false; //RED FLAG
          bool onlyPartiallyMentioned = true; // YELLOW FLAG

          var test = expressionFinder.TraverseFormalSimplified(proofProg,new ExpressionFinder.ExpressionDepth(Expression.CreateIdentExpr(outF),1)).ToList();
          // de-duplicate/turn traverseFormalToFormal
          Dictionary<string,Formal> tfs = new Dictionary<string,Formal>();
          foreach (var extendedF in test)
          {
            var name = Printer.ExprToString(extendedF.expr);
            Formal f = new Formal(extendedF.expr.tok,name,extendedF.expr.Type,true,true,extendedF.expr);
            if(!(tfs.ContainsKey(name)))
            {
              tfs.Add(name,f);
            }
            
          }
          foreach (var nestedF in tfs.Values)
          {
             var sanCheck = simpleEnsSanityCheck(desiredMethod,nestedF,true);
             deepCheck &= sanCheck;
             notMentionedAtAll |= sanCheck;
          }
          onlyPartiallyMentioned = deepCheck;
          if(!notMentionedAtAll){
            Console.WriteLine("\n-- FLAG(HIGH) -- : NONE of output ("+ outF.Name + ") are constrained by the post conditions");
          }
          else if(!onlyPartiallyMentioned){
            Console.WriteLine("\n-- FLAG(Medium) -- : Only some parts of output ("+ outF.Name + ") are constrained by the post conditions");
          }
          

        }
      Console.WriteLine("All Output Pass Sanity Check? = " + deepCheck);

 Console.WriteLine("\n------DONE------\n");
      return true;
    }

public bool simpleEnsSanityCheck(Method desiredMethod, Formal inputF,bool ret)
{
          var classStr = ret ? "(output)" : "(parameter)";
          Console.WriteLine("\tSanity check for" + classStr + " :: "+ inputF.Name);
          var fullinputF = Printer.GetFullTypeString(desiredMethod.EnclosingClass.EnclosingModuleDefinition, inputF.Type, new HashSet<ModuleDefinition>(),true);
          foreach (AttributedExpression e in desiredMethod.Ens)
          {
            Expression ee = e.E;
            var ensFormals = GetFormalsFromExpr(desiredMethod,ee);
            foreach(var f in ensFormals)
            {
              var fullF = Printer.GetFullTypeString(desiredMethod.EnclosingClass.EnclosingModuleDefinition, f.Value.Type, new HashSet<ModuleDefinition>(),true);
              // if(inputF.Name == f.Key && fullinputF == fullF)
              if(inputF.Name == f.Key)
              {
                return true;
              }
            }
          }
          Console.WriteLine("\t\tSanity Check Failed for: " + inputF.Name);
          return false;    
}

public bool simpleReqSanityCheck(Method desiredMethod, Formal inputF,bool ret)
{
          var classStr = ret ? "(output)" : "(parameter)";
          Console.WriteLine("Sanity check " + classStr + " for :: "+ inputF.Name);
          var fullinputF = Printer.GetFullTypeString(desiredMethod.EnclosingClass.EnclosingModuleDefinition, inputF.Type, new HashSet<ModuleDefinition>(),true);
          foreach (AttributedExpression e in desiredMethod.Req)
          {
            Expression ee = e.E;
            var ensFormals = GetFormalsFromExpr(desiredMethod,ee);
            foreach(var f in ensFormals)
            {
              var fullF = Printer.GetFullTypeString(desiredMethod.EnclosingClass.EnclosingModuleDefinition, f.Value.Type, new HashSet<ModuleDefinition>(),true);
              if(inputF.Name == f.Key && fullinputF == fullF)
              {
                return true;
              }
            }
          }
          Console.WriteLine("\tSanity Check Failed for: " + inputF.Name);
          return false;    
}


//       Dictionary<String, Expression> reqExprs = new Dictionary<String, Expression>();
//       var expressions = expressionFinder.ListArguments(proofProg, desiredMethod);
//       Dictionary<string, HashSet<ExpressionFinder.ExpressionDepth>> typeToExpressionDict = expressionFinder.GetRawExpressions(proofProg, desiredMethod, expressions, false);
//       var typeToExpressionDictTest = expressionFinder.GetTypeToExpressionDict(expressions);
      
//       var ezTest = expressionFinder.ListArgumentsMethodReq(proofProg,desiredMethod);
//         Dictionary<string, HashSet<ExpressionFinder.ExpressionDepth>> typeToExpressionDicTestt = expressionFinder.GetRawExpressions(proofProg, desiredMethod, ezTest, false);

//       var typeToExpressionDictTest2 = expressionFinder.GetTypeToExpressionDict(ezTest);
//       // var eliTest = expressionFinder.ListArgumentsCustom(proofProg, desiredMethod.Req[0].E);

// // Dictionary<string, HashSet<ExpressionDepth>> test = GetRawExpressions(proofProg, desiredMethod,
// //         IEnumerable<ExpressionDepth> expressions, bool addToAvailableExpressions)
//       foreach (Formal methodP in desiredMethodUnresolved.Ins)
//       {
//         Console.WriteLine("==> "+ methodP.DisplayName);
//         var formals = expressionFinder.TraverseFormal(proofProg,new ExpressionFinder.ExpressionDepth(Expression.CreateIdentExpr(methodP),1));
//       }

public async Task<bool> EvaluateMethodInPlace(Program program, Program unresolvedProgram, string funcName, string lemmaName, string proofModuleName, string baseFuncName, int depth, bool mutationsFromParams,Program proofProg, Program unresolvedProofProgram) {
      if (DafnyOptions.O.HoleEvaluatorServerIpPortList == null) {
        Console.WriteLine("ip port list is not given. Please specify with /holeEvalServerIpPortList");
        return false;
      }
      // Collect all paths from baseFunc to func
      Console.WriteLine($"{funcName} {baseFuncName} {depth}");
      if (baseFuncName == null) {
        baseFuncName = funcName;
      }
      Function baseFunc = null;
      if(proofProg != null){
       baseFunc = GetFunction(proofProg, baseFuncName);
      }else{
       baseFunc = GetFunction(program, baseFuncName);
      }

      if (baseFunc == null) {
        Console.WriteLine($"couldn't find function {baseFuncName}. List of all functions:");
        foreach (var kvp in program.ModuleSigs) {
          foreach (var topLevelDecl in ModuleDefinition.AllFunctions(kvp.Value.ModuleDef.TopLevelDecls)) {
            Console.WriteLine(topLevelDecl.FullDafnyName);
          }
        }
        return false;
      }
            dafnyVerifier = new DafnyVerifierClient(DafnyOptions.O.HoleEvaluatorServerIpPortList, $"output_{funcName}");

      CG = GetCallGraph(baseFunc);
      Function func = GetFunction(program, funcName);
      Function mutationRootFunc = GetFunction(program, DafnyOptions.O.MutationRootName);
      CurrentPath.Add(new Tuple<Function, FunctionCallExpr, Expression>(baseFunc, null, null));
      GetAllPaths(baseFunc, func);
      MCG = GetCallGraph(mutationRootFunc);
      CurrentPathMutations.Add(new Tuple<Function, FunctionCallExpr, Expression>(mutationRootFunc, null, null));
      GetAllMutationsPaths(mutationRootFunc,func);
      if (Paths.Count == 0)
        Paths.Add(new List<Tuple<Function, FunctionCallExpr, Expression>>(CurrentPath));


      UnderscoreStr = RandomString(8);
      // dafnyVerifier.sw = Stopwatch.StartNew();
      Console.WriteLine($"hole evaluation begins for func {funcName}");
      Function desiredFunction = null;
      Function desiredFunctionUnresolved = null;
      Function desiredFunctionMutationRoot = null;
      Function topLevelDeclCopy = null;
      Method desiredMethod = null;
      Method desiredMethodUnresolved = null;
      desiredFunction = GetFunction(program, funcName);



      if (desiredFunction != null) {
        includeParser = new IncludeParser(program);
        var filename = "";
        if(desiredFunction.BodyStartTok.Filename == null)
        {
          filename = includeParser.Normalized(program.FullName);
        }else{
          filename = includeParser.Normalized(desiredFunction.BodyStartTok.Filename);
        }
        foreach (var file in includeParser.GetListOfAffectedFilesBy(filename)) {
          affectedFiles.Add(file);
          affectedFiles = affectedFiles.Distinct().ToList();
        }

      if(proofProg != null){
        // dafnyVerifier.InitializeBaseFoldersInRemoteServers(proofProg, includeParser.commonPrefix);
        affectedFiles.Add(filename);
        affectedFiles = affectedFiles.Distinct().ToList();
        desiredMethod = GetMethod(program, lemmaName);
        Lemma desiredLemmm = GetLemma(proofProg, lemmaName);
        bool isLemma = desiredLemmm != null;
      if (desiredLemmm == null && desiredMethod == null) {
        Console.WriteLine($"couldn't find function {desiredLemmm}. List of all lemmas:");
        PrintAllLemmas(proofProg, lemmaName);
        Console.WriteLine($"couldn't find function {desiredMethod}. List of all methods:");
        PrintAllMethods(proofProg, lemmaName);
        return false;
      }

        includeParser = new IncludeParser(proofProg);
        // var filenameProof = "";

        dafnyVerifier.InitializeBaseFoldersInRemoteServers(proofProg, includeParser.commonPrefix);

      }else{
        dafnyVerifier.InitializeBaseFoldersInRemoteServers(program, includeParser.commonPrefix);
        affectedFiles.Add(filename);
        affectedFiles = affectedFiles.Distinct().ToList();
      }


        // expressionFinder.CalcDepthOneAvailableExpresssionsFromFunction(program, desiredFunction);
        desiredFunctionUnresolved = GetFunctionFromUnresolved(unresolvedProgram, funcName);
        desiredFunctionMutationRoot = GetFunctionFromUnresolved(unresolvedProgram,DafnyOptions.O.MutationRootName);
        desiredMethodUnresolved = GetMethodFromUnresolved(unresolvedProofProgram,lemmaName);
        if (DafnyOptions.O.HoleEvaluatorRemoveFileLine != null) {
          var fileLineList = DafnyOptions.O.HoleEvaluatorRemoveFileLine.Split(',');
          foreach (var fileLineString in fileLineList) {
            var fileLineArray = fileLineString.Split(':');
            var file = fileLineArray[0];
            var line = Int32.Parse(fileLineArray[1]);
            CodeModifier.EraseFromPredicate(desiredFunctionUnresolved as Predicate, line);
          }
        }
        Contract.Assert(desiredFunctionUnresolved != null);
        
        // Console.WriteLine("AFTER");
        topLevelDeclCopy = new Function(
          desiredFunctionUnresolved.tok, desiredFunctionUnresolved.Name, desiredFunctionUnresolved.HasStaticKeyword,
          desiredFunctionUnresolved.IsGhost, desiredFunctionUnresolved.TypeArgs, desiredFunctionUnresolved.Formals,
          desiredFunctionUnresolved.Result, desiredFunctionUnresolved.ResultType, desiredFunctionUnresolved.Req,
          desiredFunctionUnresolved.Reads, desiredFunctionUnresolved.Ens, desiredFunctionUnresolved.Decreases,
          desiredFunctionUnresolved.Body, desiredFunctionUnresolved.ByMethodTok, desiredFunctionUnresolved.ByMethodBody,
          desiredFunctionUnresolved.Attributes, desiredFunctionUnresolved.SignatureEllipsis);
      } else {
        Console.WriteLine($"{funcName} was not found!");
        return false;
      }

      DafnyOptions.O.HoleEvaluatorExpressionDepth = 10;
      // lets check 
      expressionFinder = new ExpressionFinder(this);
      int totalMutationCount = 0;
      Dictionary<ExpressionFinder.ExpressionDepth,Expression> mutatedMap = new Dictionary<ExpressionFinder.ExpressionDepth, Expression>();
      
      List<Tuple<ExpressionFinder.ExpressionDepth,Expression,bool>> inPlaceMutationList =
      new List<Tuple<ExpressionFinder.ExpressionDepth,Expression,bool>>();
      //collect all mutations (ens)
      for (int i = 0; i < desiredMethodUnresolved.Ens.Count; i++)
      {
        var e = desiredMethod.Ens[i];
        var ensList = expressionFinder.TraverseFormal(proofProg,new ExpressionFinder.ExpressionDepth(e.E,1));
        Expression ee = desiredMethodUnresolved.Ens[i].E;
        List<ExpressionFinder.ExpressionDepth> ensuresMutationList =  expressionFinder.mutateOneExpressionRevised(proofProg,desiredMethod,new ExpressionFinder.ExpressionDepth(e.E,1));
        // Console.Write(" pp = " + ee  + "\n");
        Hashtable duplicateMutationsEns = new Hashtable();
        foreach (var ed in ensuresMutationList)
        {
          if(!duplicateMutationsEns.ContainsKey(Printer.ExprToString(ed.expr)))
          {
          // availableExpressionsTemp.Add(ed);
          duplicateMutationsEns.Add(Printer.ExprToString(ed.expr),ed);
          }else{
            Console.WriteLine("Skipping (ensures) = " + Printer.ExprToString(ed.expr));
          }
        }
        // expressionFinder.availableExpressions = availableExpressionsTemp;
        ensuresMutationList = duplicateMutationsEns.Values.Cast<Microsoft.Dafny.ExpressionFinder.ExpressionDepth>().ToList();
        
        foreach (ExpressionFinder.ExpressionDepth ex in ensuresMutationList)
        {
          inPlaceMutationList.Add(new Tuple<ExpressionFinder.ExpressionDepth,Expression,bool> (ex,ee,false));
          mutatedMap.Add(ex,ee);
          // PrintExprAndCreateProcessMethodInPlace(unresolvedProgram, unresolvedProofProgram,desiredMethod,proofModuleName,ex,ee,true,false,totalMutationCount,true,true,false,desiredFunctionMutationRoot);
          totalMutationCount++;
        }
        
      }
      for (int i = 0; i < desiredMethodUnresolved.Req.Count; i++)
      {
        var r = desiredMethod.Req[i];
        var reqList = expressionFinder.TraverseFormal(proofProg,new ExpressionFinder.ExpressionDepth(r.E,1));
        Expression re = desiredMethodUnresolved.Req[i].E;
        List<ExpressionFinder.ExpressionDepth> reqsMutationList =  expressionFinder.mutateOneExpressionRevised(proofProg,desiredMethod,new ExpressionFinder.ExpressionDepth(r.E,1));
        Console.Write(" pp = " + re  + "\n");
        Hashtable duplicateMutationsReq = new Hashtable();
        foreach (var ed in reqsMutationList)
        {
          if(!duplicateMutationsReq.ContainsKey(Printer.ExprToString(ed.expr)))
          {
          // availableExpressionsTemp.Add(ed);
          duplicateMutationsReq.Add(Printer.ExprToString(ed.expr),ed);
          }else{
            Console.WriteLine("Skipping (ensures) = " + Printer.ExprToString(ed.expr));
          }
        }
        // expressionFinder.availableExpressions = availableExpressionsTemp;
        reqsMutationList = duplicateMutationsReq.Values.Cast<Microsoft.Dafny.ExpressionFinder.ExpressionDepth>().ToList();

        foreach (ExpressionFinder.ExpressionDepth ex in reqsMutationList)
        {
          inPlaceMutationList.Add(new Tuple<ExpressionFinder.ExpressionDepth,Expression,bool> (ex,re,true));
          totalMutationCount++;
        }
      }
            dafnyVerifier.sw = Stopwatch.StartNew();

        Console.WriteLine("--- START Is At Least As Weak Pass  -- ");
        for (int i = 0; i< inPlaceMutationList.Count; i++)
        {
          PrintExprAndCreateProcessMethodInPlace(unresolvedProgram, 
                                                unresolvedProofProgram,
                                                desiredMethod,
                                                desiredMethodUnresolved,
                                                proofModuleName,
                                                inPlaceMutationList.ElementAt(i).Item1,
                                                inPlaceMutationList.ElementAt(i).Item2,
                                                true,
                                                inPlaceMutationList.ElementAt(i).Item3,
                                                i,
                                                true,
                                                true,
                                                false,
                                                desiredFunctionMutationRoot);

        }
        await dafnyVerifier.startProofTasksAccordingToPriority();
       dafnyVerifier.clearTasks();
      Console.WriteLine("--- END Is At Least As Weak Pass  -- ");
            Console.WriteLine("--- START Vacuity Pass -- ");


      for(int i = 0; i < inPlaceMutationList.Count; i++)
      {
         var isWeaker = isDafnyVerifySuccessful(i);  
         var resolutionError = isResolutionError(i);
          if(!isWeaker && !resolutionError){
            Console.WriteLine("Passed (" + i + ")\n");
            // desiredFunctionUnresolved.Body = topLevelDeclCopy.Body;
            PrintExprAndCreateProcessMethodInPlace(unresolvedProgram, 
                                                unresolvedProofProgram,
                                                desiredMethod,
                                                desiredMethodUnresolved,
                                                proofModuleName,
                                                inPlaceMutationList.ElementAt(i).Item1,
                                                inPlaceMutationList.ElementAt(i).Item2,
                                                true,
                                                inPlaceMutationList.ElementAt(i).Item3,
                                                i,
                                                true,
                                                false,
                                                true,
                                                desiredFunctionMutationRoot);
          }else{
            Console.WriteLine("Failed Afer 1st PASS:  Index(" + i + ") :: IsWeaker = " + isWeaker + " :: ResolutionError= " + resolutionError);
             var requestList = dafnyVerifier.requestsList[i];
             foreach (var request in requestList){
              dafnyVerifier.dafnyOutput[request].Response = "isAtLeastAsWeak";
            }
          }
          writeOutputs(i);
      }
      await dafnyVerifier.startProofTasksAccordingToPriority();
       dafnyVerifier.clearTasks();
      Console.WriteLine("--- END Vacuity Pass  -- ");
        Console.WriteLine("--- START Full Proof Pass -- ");
        Stopwatch FullStopWatch = new Stopwatch();
        FullStopWatch.Start();
        List<int> vacIndex = new List<int>();

      for(int i = 0; i < inPlaceMutationList.Count; i++)
      {
        var isVacuous = isDafnyVerifySuccessful(i);
            var prevPassRes = dafnyVerifier.dafnyOutput[dafnyVerifier.requestsList[i].First()].Response; //isAtLeastAsWeak
            if(prevPassRes == "isAtLeastAsWeak"){
              Console.WriteLine("Failed Afer 1st PASS:  Index(" + i + ")");
            }else if(isVacuous){
                vacIndex.Add(i);
              Console.WriteLine("Failed Afer 2nd PASS:  Index(" + i + ") :: isVacuous");

            }else{
              PrintExprAndCreateProcessMethodInPlace(unresolvedProgram, 
                                                unresolvedProofProgram,
                                                desiredMethod,
                                                desiredMethodUnresolved,
                                                proofModuleName,
                                                inPlaceMutationList.ElementAt(i).Item1,
                                                inPlaceMutationList.ElementAt(i).Item2,
                                                true,
                                                inPlaceMutationList.ElementAt(i).Item3,
                                                i,
                                                true,
                                                false,
                                                false,
                                                desiredFunctionMutationRoot);
            }
      }
         await dafnyVerifier.startProofTasksAccordingToPriority();
        dafnyVerifier.clearTasks();
        Console.WriteLine("--- END Full Proof Pass -- ");
         FullStopWatch.Stop();
        Console.WriteLine("Elapsed Time is {0} ms", FullStopWatch.ElapsedMilliseconds);
      bool foundCorrectExpr = false;

      int reqPasses = 0;
      for(int i = 0; i < inPlaceMutationList.Count; i++)
      {
        UpdateCombinationResultVacAwareList(i,vacIndex.Contains(i));
        writeFinalOutputs(i);
        foundCorrectExpr = false;
        foundCorrectExpr |= combinationResults[i] == Result.FalsePredicate;
        // Console.WriteLine(foundCorrectExpr);
        var t = isDafnyVerifySuccessful(i);
        String reqOrEns = inPlaceMutationList.ElementAt(i).Item3 ? "requires " :  "ensures ";
        if(foundCorrectExpr)
        {
          Console.WriteLine("Mutation that Passes = " + i);
          Console.WriteLine("\t mutation: " + reqOrEns + Printer.ExprToString(inPlaceMutationList.ElementAt(i).Item1.expr));
          Console.WriteLine("\t orig: " + reqOrEns + Printer.ExprToString(inPlaceMutationList.ElementAt(i).Item2));
          if(inPlaceMutationList.ElementAt(i).Item3)
          {
            reqPasses++;
          }
        }else if (combinationResults[i] == Result.vacousProofPass)
        {
          Console.WriteLine("Mutation that Passes = " + i + " ** is vacous!");
          Console.WriteLine("\t mutation: " + reqOrEns + Printer.ExprToString(inPlaceMutationList.ElementAt(i).Item1.expr));
          Console.WriteLine("\t orig: " + reqOrEns + Printer.ExprToString(inPlaceMutationList.ElementAt(i).Item2));
        }
      }
      dafnyVerifier.Cleanup();    
      Console.WriteLine("--- Finish Test -- ");

      dafnyVerifier.Cleanup();
            Console.WriteLine($"{dafnyVerifier.sw.ElapsedMilliseconds / 1000} :: finish exploring, try to calculate implies graph");
      int correctProofCount = 0;
      int correctProofByTimeoutCount = 0;
      int incorrectProofCount = 0;
      int invalidExprCount = 0;
      int falsePredicateCount = 0;
      int vacousProofPass = 0;
      int noMatchingTriggerCount = 0;
      for (int i = 0; i < inPlaceMutationList.Count; i++) {
        switch (combinationResults[i]) {
          case Result.InvalidExpr: invalidExprCount++; break;
          case Result.FalsePredicate: falsePredicateCount++; break;
          case Result.CorrectProof: correctProofCount++; break;
          case Result.CorrectProofByTimeout: correctProofByTimeoutCount++; break;
          case Result.IncorrectProof: incorrectProofCount++; break;
          case Result.NoMatchingTrigger: noMatchingTriggerCount++; break;
          case Result.vacousProofPass: vacousProofPass++; break;
          case Result.Unknown: throw new NotSupportedException();
        }
      }
      Console.WriteLine("{0,-15} {1,-15} {2,-15} {3,-15} {4, -25} {5, -15}",
        "InvalidExpr", "IncorrectProof", "ProofPasses", "ReqPasses","vacousPasses","Total");
      Console.WriteLine("{0,-15} {1,-15} {2,-15} {3,-15} {4, -25}  {5, -15}",
        invalidExprCount, incorrectProofCount, falsePredicateCount, reqPasses, vacousProofPass ,  inPlaceMutationList.Count);
      string executionTimesSummary = "";
      string verboseExecTimesSummary = "";

      return true;


    }

public void UpdateCombinationResultVacAwareList(int index,bool vac) {
      var requestList = dafnyVerifier.requestsList[index];
      for(int i = 2; i<requestList.Count;i++){
          var request = requestList[i];
          var position = dafnyVerifier.requestToPostConditionPosition[request];
          var lemmaStartPosition = dafnyVerifier.requestToLemmaStartPosition[request];
          var output = dafnyVerifier.dafnyOutput[request];
          var response = output.Response;
          var filePath = output.FileName;
          var execTime = output.ExecutionTimeInMs;
          executionTimes.Add(execTime);
          verboseExecTimes.Add("(" + index + ") "+ filePath,execTime);
          if(verboseExecTimesTotal.ContainsKey(index)){
            verboseExecTimesTotal[index] = verboseExecTimesTotal[index] + execTime;
          }else{
            verboseExecTimesTotal.Add(index,execTime);
          }
          var expectedOutput =
            $"{filePath}({position},0): Error: A postcondition might not hold on this return path.";
          var expectedInconclusiveOutputStart =
            $"{filePath}({lemmaStartPosition},{validityLemmaNameStartCol}): Verification inconclusive";
                   var res = DafnyVerifierClient.IsCorrectOutput(response, expectedOutput, expectedInconclusiveOutputStart);

        if (res != Result.IncorrectProof) {
          // correctExpressions.Add(dafnyMainExecutor.processToExpr[p]);
          // Console.WriteLine(output);
          combinationResults[index] = res;
          // Console.WriteLine(p.StartInfo.Arguments);
          // Console.WriteLine(Printer.ExprToString(dafnyVerifier.requestToExpr[request]));
          Console.WriteLine(Printer.ExprToString(dafnyVerifier.requestToExpr[request]));
        } else if (response.Contains(" 0 errors\n")) {
        
        if(vac){
          // Console.WriteLine("Mutation that Passes = " + index + " ** is vacous!");
          combinationResults[index] = Result.vacousProofPass;
        }else{
          // Console.WriteLine("Mutation that Passes = " + index);
          combinationResults[index] = Result.FalsePredicate;
        }
        // break;
      }else if (response.EndsWith($"resolution/type errors detected in {Path.GetFileName(filePath)}\n")) {
          combinationResults[index] = Result.InvalidExpr;
          // break;
        } else {
          combinationResults[index] = Result.IncorrectProof;
          break;
        }
      }
      if(requestList.Count < 2)
      {
          combinationResults[index] = Result.IncorrectProof;
      }else if (requestList.Count == 2)
      {
                  combinationResults[index] = Result.vacousProofPass;

      }
 
      // }
      expressionFinder.combinationResults[index] = combinationResults[index];
    }

public async Task<bool>writeFinalOutputs(int index)
{
    var requestList = dafnyVerifier.requestsList[index];
    for(int i = 1; i<requestList.Count;i++){
      var request = requestList[i];
      var position = dafnyVerifier.requestToPostConditionPosition[request];
      var lemmaStartPosition = dafnyVerifier.requestToLemmaStartPosition[request];
      var output = dafnyVerifier.dafnyOutput[request];
      var response = output.Response;
      if (DafnyOptions.O.HoleEvaluatorCreateAuxFiles){
              if(i == 1){
                await File.AppendAllTextAsync($"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}dafnyOutput_{index}.txt", "--VAC TEST--\n"+response + "\n------\n");
              }else{
                await File.AppendAllTextAsync($"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}dafnyOutput_{index}.txt", response);
              }
      }
    }
    return true;
}
    

public async Task<bool>writeOutputs(int index)
{
    var requestList = dafnyVerifier.requestsList[index];
    for(int i = 0; i<requestList.Count;i++){
      var request = requestList[i];
      var position = dafnyVerifier.requestToPostConditionPosition[request];
      var lemmaStartPosition = dafnyVerifier.requestToLemmaStartPosition[request];
      var output = dafnyVerifier.dafnyOutput[request];
      var response = output.Response;
      if (DafnyOptions.O.HoleEvaluatorCreateAuxFiles){
              if(i == 1){
                File.AppendAllTextAsync($"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}dafnyOutput_{index}.txt", "--VAC TEST--\n"+response + "\n------\n");
              }else{
                File.AppendAllTextAsync($"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}dafnyOutput_{index}.txt", response);
              }
      }
    }
    return true;
}


  public Boolean isResolutionError(int i)
  {
    var request = dafnyVerifier.requestsList[i].First();
      var position = dafnyVerifier.requestToPostConditionPosition[request];
      var lemmaStartPosition = dafnyVerifier.requestToLemmaStartPosition[request];
      var output = dafnyVerifier.dafnyOutput[request];
      var response = output.Response;
      var filePath = output.FileName;
      // var startTime = output.StartTime;
      var execTime = output.ExecutionTimeInMs;
        executionTimes.Add(execTime);
      // startTimes.Add(startTime);
      return response.Contains("parse errors") || response.Contains("resolution/type errors") || response.Contains("Error: arguments");
  }

     public Boolean isDafnyVerifySuccessful(int i)
  {
    var request = dafnyVerifier.requestsList[i].Last();
      var position = dafnyVerifier.requestToPostConditionPosition[request];
      var lemmaStartPosition = dafnyVerifier.requestToLemmaStartPosition[request];
      var output = dafnyVerifier.dafnyOutput[request];
      var response = output.Response;
      var filePath = output.FileName;
      // var startTime = output.StartTime;
      var execTime = output.ExecutionTimeInMs;
        executionTimes.Add(execTime);
      // startTimes.Add(startTime);
      var expectedOutput =
        $"{filePath}({position},0): Error: A postcondition might not hold on this return path.";
      var expectedInconclusiveOutputStart =
        $"{filePath}({lemmaStartPosition},{validityLemmaNameStartCol}): Verification inconclusive";
      var res = DafnyVerifierClient.IsCorrectOutput(response, expectedOutput, expectedInconclusiveOutputStart);
      return response.EndsWith("0 errors\n");
  }

   public static string GetBaseLemmaListMutationList(Program program,Function fn, ModuleDefinition currentModuleDef,List<Tuple<Function, FunctionCallExpr, Expression>> path) {
      string res = "";
      // add all predicates in path
      foreach (var nwPair in path)
      {
          using (var wr = new System.IO.StringWriter()) {
          var pr = new Printer(wr);
          pr.ModuleForTypes = currentModuleDef;
          pr.PrintFunction(nwPair.Item1, 0,false);
          res += wr.ToString();
        }
      res += "\n\n";
      }
    // annotate with "BASE_"
    foreach (var nwPair in path)
    {
      var indecies = AllIndexesOf(res,nwPair.Item1.Name+"(");
      foreach (var index in indecies.Reverse())
      {
        res = res.Insert(index, "BASE_");
      }
    }
    // add "mutated" intermediate predicates
    // for (int i = 0; i < path.Count - 1; i++)
    // {
    //   var nwPair = path[i];
    //   using (var wr = new System.IO.StringWriter()) {
    //       var pr = new Printer(wr);
    //       pr.ModuleForTypes = currentModuleDef;
    //       pr.PrintFunction(nwPair.Item1, 0,false);
    //       res += wr.ToString();
    //     }
    //   res += "\n\n";
    // }

      return res;
    }

   public static string GetBaseLemmaList(Function fn, ModuleDefinition currentModuleDef) {
      string res = "";
      // res += RemoveWhitespace(Printer.FunctionSignatureToString(fn));
      res += "\n{\n";
      res += Printer.ExprToString(fn.Body);
      res += "\n}";
      // return res;
      // Console.WriteLine(fn.Name);
        using (var wr = new System.IO.StringWriter()) {
        var pr = new Printer(wr);
        pr.ModuleForTypes = currentModuleDef;
        pr.PrintFunction(fn, 0,false);
        res = wr.ToString();
      }
      int i = res.IndexOf(fn.Name);
      String modStr1 = res.Insert(i, "BASE_");
      return modStr1;
    }

    public static string getVacuityLemma(Lemma l)
    {
      string res = "";
      // res += Printer.ExprToString(baseLemma.Body);
      using (var wr1 = new System.IO.StringWriter()) {
        var pr1 = new Printer(wr1);
        pr1.PrintMethod(l, 0,false);
        // Console.WriteLine(wr1.ToString());
        res = wr1.ToString();
      }
      int d = res.IndexOf("decreases");
     foreach (var e in l.Ens) {
        Console.WriteLine( Printer.ExprToString(e.E));
     }
      
      if(d == -1){
        int i = res.IndexOf("{");
        res = res.Insert(i-1, "ensures false;\n");
      }else{
        res = res.Insert(d-1, "ensures false;\n");
      }
      return res;
    }

    public static string GetIsSameLemmaList(Function fn,List<Tuple<Function, FunctionCallExpr, Expression>> path, ModuleDefinition currentModuleDef, Expression constraintExpr,Boolean isQuantifier) {
      string res = "lemma isSame";
       foreach (var nwPair in path) {
        res += "_" + nwPair.Item1.Name;
      }
      res += "(";
      var sep = "";
      var p = "";
       Tuple<string, string> x = new Tuple<string, string>(null, null);
      foreach (var nwPair in path) {
        res += sep + " ";
        sep = "";
        x = GetFunctionParamList(nwPair.Item1);
        res += x.Item2;
        p += "" + x.Item1; 
        sep = ", ";
      }
      res += ")\n";
      foreach (var req in path[0].Item1.Req) {
       if(isQuantifier){
          res += "  requires forall " + x.Item2 + " :: "+ GetNonPrefixedString(req.E, currentModuleDef) + "\n";
        }else{
          res += "  requires " + GetNonPrefixedString(req.E, currentModuleDef) + "\n";
        }
      }
       if(p != ""){
        res += "  ensures forall " + p + " :: "+ fn.Name+ "_BASE("+p+") <==> " + fn.Name+"("+p+")\n{}";
       }else{
              res += "  ensures " + fn.Name+ "_BASE() <==> " + fn.Name+"()\n{}";
       }
      return res;
    }

    public static string GetIsWeaker(Function fn,List<Tuple<Function, FunctionCallExpr, Expression>> path, ModuleDefinition currentModuleDef, Expression constraintExpr, Boolean isQuantifier) {
      string res = "lemma isAtLeastAsWeak";
      //  foreach (var nwPair in path) {
      //   res += "_" + nwPair.Item1.Name;
      // }
       res += "_" + path.Last().Item1.Name;
      foreach(var t in fn.TypeArgs)
      {
        res += "<"+t+"(0,!new)>";
        // Console.WriteLine("a = " + t);
      }
      res += "(";
      var sep = "";
      var p = "";
      Tuple<string, string> x = new Tuple<string, string>(null, null);

      // foreach (var nwPair in path) {
      //   res += sep + " ";
      //   sep = "";
      //   x = GetFunctionParamList(nwPair.Item1);
      //   res += x.Item2;
      //   p += "" + x.Item1; 
      //   sep = ", ";
      // }
        res += sep + " ";
        sep = "";
        x = GetFunctionParamListSpec(path.Last().Item1);
        
        res += x.Item2;
        p += "" + x.Item1; 
        sep = ", ";
      res += ")\n";
      // if(p != ""){
      //   res += "requires " + fn.Name+"_BASE("+p+")\n";
      // }
      foreach (var req in path.Last().Item1.Req) {
        // res += "  requires " + GetPrefixedString(path[0].Item1.Name + "_", req.E, currentModuleDef) + "\n";
        
        if(isQuantifier){
          res += "  requires forall " + x.Item2 + " :: "+ GetNonPrefixedString(req.E, currentModuleDef) + "\n";
        }else{
          res += "  requires " + GetNonPrefixedString(req.E, currentModuleDef) + "\n";
        }
      }
      if(p != ""){
        res += "requires BASE_" + fn.Name+"("+p+")\n";
      }
      if(p != ""){
        // res += "  ensures forall " + p + " :: "+ fn.Name+"_BASE("+p+") ==> " + fn.Name+"("+p+")\n{}";
        res += "ensures " + fn.Name+"("+p+")\n{}\n";
      }else{
        // res += "  ensures BASE_" + fn.Name+"() ==> " + fn.Name+"()\n{}";
        res += "  ensures " + fn.Name+"() ==> BASE_" + fn.Name+"()\n{}";


      }
      return res;
    }

    public static string GetIsWeakerMethodInPlace(Method method,List<Tuple<Function, FunctionCallExpr, Expression>> path, ModuleDefinition currentModuleDef, Expression constraintExpr,bool isReq)
    {
      string res = "lemma isAtLeastAsWeak";
      var paramsAndBodies = GetExtraOldParams(method,null,null,null);

       res += "_" + path[0].Item1.Name;
      foreach(var t in method.TypeArgs)
      {
        res += "<"+t+"(0,!new)>";
      }
      res += "(";
      var sep = "";
      var p = "";
      Tuple<string, string> x = new Tuple<string, string>(null, null);
      res += sep + " ";
        sep = "";
        // foreach (string param in paramsAndBodies[2])
        // {
        //   res += param + ", ";
        // }
        foreach (string param in paramsAndBodies[0])
        {
          res += param + ", ";
        }
        x = GetMethodParamListSpec(method);
        res += x.Item2;
        p += "" + x.Item1; 
        sep = ", ";
      res += ")\n";
      string newParamNames = "";
        //   foreach (string param in paramsAndBodies[2])
        // {
        // newParamNames += param.Substring(0,param.IndexOf(":")) + ", ";
        // }
      foreach (string param in paramsAndBodies[0])
        {
          newParamNames += param.Substring(0,param.IndexOf(":")) + ", ";
        }
  
      // newParamNames = newParamNames.Remove(newParamNames.Length-1,1);
      if(p != ""){
        if(!isReq)
        {
          foreach (AttributedExpression e in method.Req)
          {
            Expression ee = e.E;
            //update requires to match "Old" 
            string reqExprStr = Printer.ExprToString(ee);
            // check all extra params
            foreach (string newP in paramsAndBodies[0])
            {
              if(newP.Contains("_OLD")){
              var nameS = newP.Substring(0,newP.IndexOf("_OLD"));
              if(reqExprStr.Contains(nameS+".") || reqExprStr.Contains(nameS+")") || reqExprStr.Contains(nameS+","))
              {
                reqExprStr = reqExprStr.Replace(nameS+".",nameS+"_OLD.");
                reqExprStr = reqExprStr.Replace(nameS+")",nameS+"_OLD)");
                reqExprStr = reqExprStr.Replace(nameS+",",nameS+"_OLD,");
              }
              }
            }
            res += "requires " +  reqExprStr + "\n";
          }
          res += "requires BASE_" + method.Name+"_Pred("+newParamNames+p+")\n";
          res += "ensures MUTATED_" + method.Name+"_Pred("+newParamNames+p+")\n{}\n";
        }else{
          //if testing the req, we want to exclude "stronger" mutationss
          res += "requires MUTATED_" + method.Name+"_Pred("+newParamNames+p+")\n";
          res += "ensures BASE_" + method.Name+"_Pred("+newParamNames+p+")\n{}\n";
        }
        
      }
      return res;
    }

    public static string GetIsSimpleVacTest(Method method,List<Tuple<Function, FunctionCallExpr, Expression>> path, ModuleDefinition currentModuleDef, Expression constraintExpr,bool isReq)
    {
      string res = "lemma isVac";
      var paramsAndBodies = GetExtraOldParams(method,null,null,null);

       res += "_" + path[0].Item1.Name;
      foreach(var t in method.TypeArgs)
      {
        res += "<"+t+"(0,!new)>";
      }
      res += "(";
      var sep = "";
      var p = "";
      Tuple<string, string> x = new Tuple<string, string>(null, null);
      res += sep + " ";
        sep = "";
        // foreach (string param in paramsAndBodies[2])
        // {
        //   res += param + ", ";
        // }
        foreach (string param in paramsAndBodies[0])
        {
          res += param + ", ";
        }
        x = GetMethodParamListSpec(method);
        res += x.Item2;
        p += "" + x.Item1; 
        sep = ", ";
      res += ")\n";
      string newParamNames = "";
        //   foreach (string param in paramsAndBodies[2])
        // {
        // newParamNames += param.Substring(0,param.IndexOf(":")) + ", ";
        // }
      foreach (string param in paramsAndBodies[0])
        {
          newParamNames += param.Substring(0,param.IndexOf(":")) + ", ";
        }
  
      // newParamNames = newParamNames.Remove(newParamNames.Length-1,1);
      if(p != ""){
        if(!isReq)
        {
           foreach (AttributedExpression e in method.Req)
        {
          Expression ee = e.E;
          //update requires to match "Old" 
          string reqExprStr = Printer.ExprToString(ee);
          // check all extra params
          foreach (string newP in paramsAndBodies[0])
          {
            if(newP.Contains("_OLD")){
              var nameS = newP.Substring(0,newP.IndexOf("_OLD"));
              if(reqExprStr.Contains(nameS+".") || reqExprStr.Contains(nameS+")") || reqExprStr.Contains(nameS+","))
              {
                reqExprStr = reqExprStr.Replace(nameS+".",nameS+"_OLD.");
                reqExprStr = reqExprStr.Replace(nameS+")",nameS+"_OLD)");
                reqExprStr = reqExprStr.Replace(nameS+",",nameS+"_OLD,");
              }
            }
          }
          res += "requires " +  reqExprStr + "\n";
        }
        }
        res += "requires MUTATED_" + method.Name+"_Pred("+newParamNames+p+")\n";
        res += "ensures false\n{}\n";
      }
      return res;
    }

    public static List<List<string>> GetExtraOldParams(Method method, ModuleDefinition currentModuleDef,Expression orig,Expression mutated)
    {
      List<List<string>> paramsAndBodys = new List<List<string>>();
      List<string> extraParams = new List<string>();
      List<string> bodyExprs = new List<string>();
      List<string> heapParams = new List<string>();
      HashSet<string> insSet = new HashSet<string>();
      List<string> returns = new List<string>();
      foreach(var f in method.Ins)
      {
        insSet.Add(f.Name);
      }

      foreach (AttributedExpression e in method.Ens)
        {
         Expression ee = e.E;

        var eFormals = GetFormalsFromExpr(method,ee);
         if(mutated != null && Printer.ExprToString(ee) == Printer.ExprToString(orig))
         {
          ee = mutated;
         }
         var ensOld = IfExprContainsOldExpr(method,ee);
         var ensOldList = IfExprContainsOldExprList(method,ee);
         if(ensOldList != null)
         {
          var removedOld = Printer.ExprToString(ee);
          foreach (var ensOldValue in ensOldList.Values)
          {
             
            if(ensOldValue.Item1.IndexOf(".") > 0)
            {
              removedOld = removedOld.Replace("old("+ensOldValue.Item3.Substring(0,ensOldValue.Item3.IndexOf("_OLD")),"("+ensOldValue.Item3);
            }else{
              removedOld = removedOld.Replace(ensOldValue.Item1,ensOldValue.Item3);
            }
            
            //updated Params
            // var ensOldValuePrefix = ensOldValue.Item3.Substring(0,ensOldValue.Item3.IndexOf("_OLD"));
            var updatedP = ensOldValue.Item3+":"+ensOldValue.Item2;
            if(!extraParams.Contains(updatedP)){
              extraParams.Add(updatedP);
            }
          }
          bodyExprs.Add(removedOld);
            // //strip "OLD()
            // var removedOld = "";
            // if(ensOld.Item1.IndexOf(".") > 0)
            // {
            //   removedOld = Printer.ExprToString(ee).Replace("old("+ensOld.Item3.Substring(0,ensOld.Item3.IndexOf("_OLD")),"("+ensOld.Item3);
            // }else{
            //   removedOld = Printer.ExprToString(ee).Replace(ensOld.Item1,ensOld.Item3);
            // }
            // bodyExprs.Add(removedOld);
            // //updated Params
            // var ensOldPrefix = ensOld.Item3.Substring(0,ensOld.Item3.IndexOf("_OLD"));
            // var updatedP = ensOld.Item3+":"+ensOld.Item2;
            // if(!extraParams.Contains(updatedP)){
            //   extraParams.Add(updatedP);
            // }
         }
         else{
            bodyExprs.Add(Printer.ExprToString(ee));
         }
          // check params for "new ones"
          foreach (var kvp in eFormals)
          {
            if (!insSet.Contains(kvp.Key))
            {
              //  Console.WriteLine("--> " + kvp.Key);
               var updatedFormalP = kvp.Key+":"+Printer.GetFullTypeString(method.EnclosingClass.EnclosingModuleDefinition, kvp.Value.Type, new HashSet<ModuleDefinition>(),true);
              if(!heapParams.Contains(updatedFormalP)){
              heapParams.Add(updatedFormalP);
            }
            }
          }
          // foreach (var origF in method.Ins)
          // {
          //   if(! eFormals.ContainsKey(origF.Name) )
          //   {
          //     Console.WriteLine("--> " + origF.Name);
          //     extraParams.Add("")
          //   }
          // }
        }
        foreach (var ret in method.Outs)
      {
        // var getType = GetPrefixedStringType("", ret.Type,method.EnclosingClass.EnclosingModuleDefinition);
          var resovledReturns = ret.Name+":"+Printer.GetFullTypeString(method.EnclosingClass.EnclosingModuleDefinition, ret.Type, new HashSet<ModuleDefinition>(),true);
          returns.Add(resovledReturns);
          extraParams.Add(resovledReturns);
          // Console.WriteLine(resovledReturns);
        }
  
        paramsAndBodys.Add(extraParams);
        paramsAndBodys.Add(bodyExprs);
        paramsAndBodys.Add(heapParams);
      return paramsAndBodys;

    }

    public static string GetPrefixedStringType(string prefix,Type type, ModuleDefinition currentModuleDef) {
      using (var wr = new System.IO.StringWriter()) {
        var pr = new Printer(wr);
        pr.Prefix = prefix;
        pr.ModuleForTypes = currentModuleDef;
        pr.PrintType(type);
        return wr.ToString();
      }
    }

      public static string GetIsBasePredMethodInPlace(Method method,List<Tuple<Function, FunctionCallExpr, Expression>> path, ModuleDefinition currentModuleDef, Expression constraintExpr,Boolean isReq)
    {
      string res = "predicate BASE_"+ method.Name+"_Pred";
      var paramsAndBodies = GetExtraOldParams(method,currentModuleDef,null,null);

      if(isReq)
      {
        res += "(";
        var sep = "";
        var p = "";
        foreach (string newP in paramsAndBodies[0])
          {
            res += newP + ",";
          }
        Tuple<string, string> x = new Tuple<string, string>(null, null);
        res += sep + " ";
          sep = "";
          x = GetMethodParamListSpec(method);
          res += x.Item2;
          p += "" + x.Item1; 
          sep = ", ";
        res += ")\n";
        res += "reads * \n";
          res += "{\n";

         foreach (AttributedExpression e in method.Req)
        {
          Expression ee = e.E;
         res += "&& " +  Printer.ExprToString(ee) + "\n";
        }
        res += "}\n";
      }else{
        // need to work backwards to know what OLD to update

          res += "(";
          var sep = "";
          var p = "";
          // foreach (string newP in paramsAndBodies[2])
          // {
          //   res += newP + ",";
          // }
          foreach (string newP in paramsAndBodies[0])
          {
            res += newP + ",";
          }
          Tuple<string, string> x = new Tuple<string, string>(null, null);
          res += sep + " ";
          sep = "";
          x = GetMethodParamListSpec(method);
          res += x.Item2;
          p += "" + x.Item1; 
          sep = ", ";
          res += ")\n";
          res += "reads * \n";

        foreach (AttributedExpression e in method.Req)
        {
          Expression ee = e.E;
          //update requires to match "Old" 
          string reqExprStr = Printer.ExprToString(ee);
          // check all extra params
          foreach (string newP in paramsAndBodies[0])
          {
            if(newP.Contains("_OLD")){
              var nameS = newP.Substring(0,newP.IndexOf("_OLD"));
              if(reqExprStr.Contains(nameS+".") || reqExprStr.Contains(nameS+")") || reqExprStr.Contains(nameS+","))
              {
                reqExprStr = reqExprStr.Replace(nameS+".",nameS+"_OLD.");
                reqExprStr = reqExprStr.Replace(nameS+")",nameS+"_OLD)");
                reqExprStr = reqExprStr.Replace(nameS+",",nameS+"_OLD,");
              }
            }
          }
          res += "requires " +  reqExprStr + "\n";
        }
        res += "{\n";
        foreach (string bodyE in paramsAndBodies[1])
        {
          res += "&& (" +  bodyE + ")\n";
        }
        //  res += "&& " +  Printer.ExprToString(ee) + "\n";
        res += "}\n";
      }
      return res;
    }

public static string GetIsMutatedPredMethodInPlace(Method method,List<Tuple<Function, FunctionCallExpr, Expression>> path, ModuleDefinition currentModuleDef, Expression constraintExpr,Boolean isReq,Expression orig, Expression mutataed)
    {
      string res = "predicate MUTATED_"+ method.Name+"_Pred";
      var paramsAndBodies = GetExtraOldParams(method,currentModuleDef,orig,mutataed);

      if(isReq)
      {
        res += "(";
        var sep = "";
        var p = "";
        foreach (string newP in paramsAndBodies[0])
          {
            res += newP + ",";
          }
        Tuple<string, string> x = new Tuple<string, string>(null, null);
        res += sep + " ";
          sep = "";
          x = GetMethodParamListSpec(method);
          res += x.Item2;
          p += "" + x.Item1; 
          sep = ", ";
        res += ")\n";
        res += "reads * \n";
          res += "{\n";

         foreach (AttributedExpression e in method.Req)
        {
          Expression ee = e.E;
          if (Printer.ExprToString(ee) == Printer.ExprToString(orig))
         {
          // Console.WriteLine("sadfasdf");
          ee = mutataed;
         }
         res += "&& " +  Printer.ExprToString(ee) + "\n";
        }
        res += "}\n";
      }else{
        // need to work backwards to know what OLD to update

          res += "(";
          var sep = "";
          var p = "";
        // foreach (string newP in paramsAndBodies[2])
        //   {
        //     res += newP + ",";
        //   }
          foreach (string newP in paramsAndBodies[0])
          {
            res += newP + ",";
          }
          Tuple<string, string> x = new Tuple<string, string>(null, null);
          res += sep + " ";
          sep = "";
          x = GetMethodParamListSpec(method);
          res += x.Item2;
          p += "" + x.Item1; 
          sep = ", ";
          res += ")\n";
          res += "reads * \n";

        foreach (AttributedExpression e in method.Req)
        {
          Expression ee = e.E;
          //update requires to match "Old" 
          string reqExprStr = Printer.ExprToString(ee);
          // check all extra params
          foreach (string newP in paramsAndBodies[0])
          {
            if(newP.Contains("_OLD")){
              var nameS = newP.Substring(0,newP.IndexOf("_OLD"));
              if(reqExprStr.Contains(nameS+".") || reqExprStr.Contains(nameS+")") || reqExprStr.Contains(nameS+","))
                {
                  reqExprStr = reqExprStr.Replace(nameS+".",nameS+"_OLD.");
                  reqExprStr = reqExprStr.Replace(nameS+")",nameS+"_OLD)");
                  reqExprStr = reqExprStr.Replace(nameS+",",nameS+"_OLD,");
                }
            }
            }
          res += "requires " +  reqExprStr + "\n";
        }
        res += "{\n";
        if(mutataed is OldExpr)
        {

        }else{
          
        }
        foreach (string bodyE in paramsAndBodies[1])
        {
          res += "&& (" +  bodyE + ")\n";
        }
        //  res += "&& " +  Printer.ExprToString(ee) + "\n";
        res += "}\n";
      }
      return res;
    }

    public static Dictionary<string,Formal> GetFormalsFromExpr(Method meth, Expression e)
    {
      Dictionary<string,Formal> fMap = new Dictionary<string,Formal>();
      HashSet<string> boundVars = new HashSet<string>();
      if(e is OldExpr) //handled elsewhere
      {
        return fMap;
      }
      if(e is ForallExpr)
      {
        ForallExpr fe = e as ForallExpr;
        foreach (var bv in fe.AllBoundVars)
        {
          boundVars.Add(bv.Name);
        }
      }
    if(e is ExistsExpr)
      {
        ExistsExpr ee = e as ExistsExpr;
        foreach (var bv in ee.AllBoundVars)
        {
          boundVars.Add(bv.Name);
        }
      }
      if(e is NameSegment )
      {
        NameSegment ns = e as NameSegment;
        Formal f = new Formal(ns.tok,ns.Name as string, ns.Type, true,true,e);
        if(!fMap.ContainsKey(ns.Name))
        {
          fMap.Add(ns.Name,f);
        }
      }
      else if(e is ExprDotName){
        ExprDotName de = e as ExprDotName;
        var deName = Printer.ExprToString(de);
        Formal f = new Formal(de.tok,deName,de.Type,true,true,e);
        if(!fMap.ContainsKey(deName))
        {
          fMap.Add(deName,f);
        }

      }else if(e is UnaryOpExpr && (e as UnaryOpExpr).Op == UnaryOpExpr.Opcode.Cardinality)
      {
        var ue = e as UnaryOpExpr;
        var ueName = Printer.ExprToString(ue);
        Formal f = new Formal(ue.tok,ueName,ue.Type,true,true,e);
        if(!fMap.ContainsKey(ueName))
        {
          fMap.Add(ueName,f);
        }
      }else{
        var subE = e.SubExpressions;
        // var r = false;
        foreach (Expression subEE in subE)
        {
          var subMap = GetFormalsFromExpr(meth,subEE);
          foreach (var kvp in subMap)
          {
            if(!fMap.ContainsKey(kvp.Key))
            {
              fMap.Add(kvp.Key,kvp.Value);
            }
          }
        }
      }
      // remove bound var
      if(boundVars.Count > 0)
      {
        foreach (var bv in boundVars)
        {
          if(fMap.ContainsKey(bv))
          {
            fMap.Remove(bv);
          }
        }
      }
      return fMap;
    }

    public static Dictionary<string,Tuple<string, string, string>> IfExprContainsOldExprList(Method meth,Expression e)
    {
      Dictionary<string,Tuple<string, string, string>> listOfTups = new Dictionary<string,Tuple<string, string, string>>();
      Tuple<string, string,string> x = new Tuple<string, string,string>(null, null,null);
      if(e is OldExpr)
      {
        // return true;
        string it3 = Printer.ExprToString(e.SubExpressions.First())+"_OLD";

        if(e.SubExpressions.First() is ExprDotName)
        {
        var subLhs = e.SubExpressions.First();
        while (subLhs is ExprDotName)
        {
          var tempLhs = (subLhs as ExprDotName).Lhs;
          if(tempLhs is ExprDotName){
            subLhs = tempLhs;
          }else{
            break;
          }
        }

          string lhs = Printer.ExprToString((e.SubExpressions.First() as ExprDotName).Lhs);
          string subLhsStr =Printer.ExprToString((subLhs as ExprDotName).Lhs);
          it3 = subLhsStr + "_OLD";
          // manual workaround
          string fType = Printer.GetFullTypeString(meth.EnclosingClass.EnclosingModuleDefinition, (subLhs as ExprDotName).Lhs.Type, new HashSet<ModuleDefinition>(),false);
          // string fType = Printer.GetFullTypeString(meth.EnclosingClass.EnclosingModuleDefinition, (e.SubExpressions.First() as ExprDotName).Lhs.Type, new HashSet<ModuleDefinition>(),false);
          if(fType.Contains("ICryptographicMaterialsManagerCallHistory"))
          {
            fType = fType.Replace("ICryptographicMaterialsManagerCallHistory","ICryptographicMaterialsManager");
          }
          //
          x = new Tuple<string, string, string>( Printer.ExprToString(e),fType,it3);
          listOfTups.Add(Printer.ExprToString(e),x);
          return  listOfTups;
          // it3 = Printer.ExprToString(e.SubExpressions.First()).Replace(lhs,lhs+"_OLD");
        }
        x = new Tuple<string, string, string>( Printer.ExprToString(e),Printer.GetFullTypeString(meth.EnclosingClass.EnclosingModuleDefinition, e.Type, new HashSet<ModuleDefinition>(),true),it3);
        listOfTups.Add(Printer.ExprToString(e),x);
        return  listOfTups;
      }
      else
      {
        var subE = e.SubExpressions;
        // var r = false;
        foreach (Expression subEE in subE)
        {
          if(x.Item1 == null){
            var subDictionary = IfExprContainsOldExprList(meth,subEE);
            foreach (var subT in subDictionary.Keys)
            {
              if(!listOfTups.ContainsKey(subT))
              {
                listOfTups.Add(subT,subDictionary[subT]);
              }
            }
            // listOfTups.AddRange(IfExprContainsOldExprList(meth,subEE));
          }
        }
        return listOfTups;
        // return e;
      }
    }


    public static Tuple<string, string, string> IfExprContainsOldExpr(Method meth,Expression e)
    {
      Tuple<string, string,string> x = new Tuple<string, string,string>(null, null,null);
      if(e is OldExpr)
      {
        // return true;
        string it3 = Printer.ExprToString(e.SubExpressions.First())+"_OLD";

        if(e.SubExpressions.First() is ExprDotName)
        {
        var subLhs = e.SubExpressions.First();
        while (subLhs is ExprDotName)
        {
          var tempLhs = (subLhs as ExprDotName).Lhs;
          if(tempLhs is ExprDotName){
            subLhs = tempLhs;
          }else{
            break;
          }
        }

          string lhs = Printer.ExprToString((e.SubExpressions.First() as ExprDotName).Lhs);
          string subLhsStr =Printer.ExprToString((subLhs as ExprDotName).Lhs);
          it3 = subLhsStr + "_OLD";
          // manual workaround
          string fType = Printer.GetFullTypeString(meth.EnclosingClass.EnclosingModuleDefinition, (subLhs as ExprDotName).Lhs.Type, new HashSet<ModuleDefinition>(),false);
          // string fType = Printer.GetFullTypeString(meth.EnclosingClass.EnclosingModuleDefinition, (e.SubExpressions.First() as ExprDotName).Lhs.Type, new HashSet<ModuleDefinition>(),false);
          if(fType.Contains("ICryptographicMaterialsManagerCallHistory"))
          {
            fType = fType.Replace("ICryptographicMaterialsManagerCallHistory","ICryptographicMaterialsManager");
          }
          //
          x = new Tuple<string, string, string>( Printer.ExprToString(e),fType,it3);
          return  x;
          // it3 = Printer.ExprToString(e.SubExpressions.First()).Replace(lhs,lhs+"_OLD");
        }
        x = new Tuple<string, string, string>( Printer.ExprToString(e),Printer.GetFullTypeString(meth.EnclosingClass.EnclosingModuleDefinition, e.Type, new HashSet<ModuleDefinition>(),true),it3);
        return  x;
      }
      else
      {
        var subE = e.SubExpressions;
        // var r = false;
        foreach (Expression subEE in subE)
        {
          if(x.Item1 == null){
            x = IfExprContainsOldExpr(meth,subEE);
          }
        }
        return x;
        // return e;
      }
    }

    public static string GetIsWeakerMutationsRoot(Function fn,List<Tuple<Function, FunctionCallExpr, Expression>> path, ModuleDefinition currentModuleDef, Expression constraintExpr, Boolean isQuantifier) {
      string res = "lemma isAtLeastAsWeak";
       res += "_" + path[0].Item1.Name;
      foreach(var t in fn.TypeArgs)
      {
        res += "<"+t+"(0,!new)>";
      }
      res += "(";
      var sep = "";
      var p = "";
      Tuple<string, string> x = new Tuple<string, string>(null, null);

        res += sep + " ";
        sep = "";
        x = GetFunctionParamListSpec(path[0].Item1);
        
        res += x.Item2;
        p += "" + x.Item1; 
        sep = ", ";
      res += ")\n";
      // if(p != ""){
      //   res += "requires " + fn.Name+"_BASE("+p+")\n";
      // }
      foreach (var req in path[0].Item1.Req) {
        // res += "  requires " + GetPrefixedString(path[0].Item1.Name + "_", req.E, currentModuleDef) + "\n";
        
        if(isQuantifier){
          res += "  requires forall " + x.Item2 + " :: "+ GetNonPrefixedString(req.E, currentModuleDef) + "\n";
        }else{
          res += "  requires " + GetNonPrefixedString(req.E, currentModuleDef) + "\n";
        }
      }
      if(p != ""){
        res += "requires BASE_" + fn.Name+"("+p+")\n";
      }
      if(p != ""){
        // res += "  ensures forall " + p + " :: "+ fn.Name+"_BASE("+p+") ==> " + fn.Name+"("+p+")\n{}";
        res += "ensures " + fn.Name+"("+p+")\n{}\n";
      }else{
        res += "  ensures " + fn.Name+"() ==> BASE_" + fn.Name+"()\n{}";

      }
      return res;
    }


    public static string getVacuityLemmaRevised(Function fn,List<Tuple<Function, FunctionCallExpr, Expression>> path, ModuleDefinition currentModuleDef, Expression constraintExpr, Boolean isQuantifier) {
      string res = "lemma isVac";
      //  foreach (var nwPair in path) {
      //   res += "_" + nwPair.Item1.Name;
      
      // }
       res += "_" + path.Last().Item1.Name;
      foreach(var t in fn.TypeArgs)
      {
        res += "<"+t+"(0,!new)>";
        // Console.WriteLine("a = " + t);
      }
      res += "(";
      var sep = "";
      var p = "";
      Tuple<string, string> x = new Tuple<string, string>(null, null);

      // foreach (var nwPair in path) {
      //   res += sep + " ";
      //   sep = "";
      //   x = GetFunctionParamList(nwPair.Item1);
      //   res += x.Item2;
      //   p += "" + x.Item1; 
      //   sep = ", ";
      // }
        res += sep + " ";
        sep = "";
        x = GetFunctionParamList(path.Last().Item1);
        res += x.Item2;
        p += "" + x.Item1; 
        sep = ", ";
      res += ")\n";
      // if(p != ""){
      //   res += "requires " + fn.Name+"_BASE("+p+")\n";
      // }
      foreach (var req in path.Last().Item1.Req) {
        // res += "  requires " + GetPrefixedString(path[0].Item1.Name + "_", req.E, currentModuleDef) + "\n";
        
        if(isQuantifier){
          res += "  requires forall " + x.Item2 + " :: "+ GetNonPrefixedString(req.E, currentModuleDef) + "\n";
        }else{
          res += "  requires " + GetNonPrefixedString(req.E, currentModuleDef) + "\n";
        }
      }
      if(p != ""){
        res += "\t requires " + fn.Name+"("+p+")\n";
      }
      res += "\t ensures false;\n{}";
      return res;
    }

    public static string GetIsStronger(Function fn,List<Tuple<Function, FunctionCallExpr, Expression>> path, ModuleDefinition currentModuleDef, Expression constraintExpr, Boolean isQuantifier) {
      string res = "lemma isStronger";
       foreach (var nwPair in path) {
        res += "_" + nwPair.Item1.Name;
      }
      res += "(";
      var sep = "";
      var p = "";
      Tuple<string, string> x = new Tuple<string, string>(null, null);

      foreach (var nwPair in path) {
        res += sep + " ";
        sep = "";
        x = GetFunctionParamList(nwPair.Item1);
        res += x.Item2;
        p += "" + x.Item1; 
        sep = ", ";
      }
      res += ")\n";
      foreach (var req in path[0].Item1.Req) {
        // Console.WriteLine("  requires forall " + x.Item2 + " :: "+ GetNonPrefixedString(req.E, currentModuleDef) + "\n");
        // res += "  requires " + GetPrefixedString(path[0].Item1.Name + "_", req.E, currentModuleDef) + "\n";
        if(isQuantifier){
          res += "  requires forall " + x.Item2 + " :: "+ GetNonPrefixedString(req.E, currentModuleDef) + "\n";
        }else{
          res += "  requires " + GetNonPrefixedString(req.E, currentModuleDef) + "\n";
        }
      }
      if(p != ""){
        res += "  ensures forall " + p + " :: "+ fn.Name+ "("+p+") ==> " + fn.Name+"_BASE("+p+")\n{}";
      }else{
        res += "  ensures " + fn.Name+ "() ==> " + fn.Name+"_BASE()\n{}";

      }
      return res;
    }


 public static string GetValidityLemma(List<Tuple<Function, FunctionCallExpr, Expression>> path, ModuleDefinition currentModuleDef, Expression constraintExpr, int cnt, int id) {
      string res = "lemma {:timeLimitMultiplier 2} validityCheck";
      if (cnt != -1) {
        res += "_" + cnt.ToString();
      }
      foreach (var nwPair in path) {
        res += "_" + nwPair.Item1.Name;
      }
      res += "_" + id;
            foreach(var t in path.Last().Item1.TypeArgs)
      {
        res += "<"+t+"(0,!new)>";
        // Console.WriteLine("a = " + t);
      }
      res += "(";
      var sep = "";
      foreach (var nwPair in path) {
        res += sep + "\n    ";
        sep = "";
        res += GetFunctionParamList(nwPair.Item1, nwPair.Item1.Name + "_").Item2;
        sep = ", ";
      }
      res += ")\n";
      foreach (var req in path[0].Item1.Req) {
        res += "  requires " + GetPrefixedString(path[0].Item1.Name + "_", req.E, currentModuleDef) + "\n";
      }
      res += "  requires " + path[0].Item1.FullDafnyName + "(";
      sep = "";
      foreach (var formal in path[0].Item1.Formals) {
        res += sep + path[0].Item1.Name + "_" + formal.Name;
        sep = ", ";
      }
      res += ")\n";
      for (int i = 0; i < path.Count - 1; i++) {
        var callExpr = path[i + 1].Item2;
        var condExpr = path[i + 1].Item3;
        var requiresOrAndSep = "requires";
        if (condExpr != null) {
          if (condExpr is BinaryExpr && (condExpr as BinaryExpr).E1 is LetExpr) {
            requiresOrAndSep = "  &&";
          }
          currentModuleDef = path[i].Item1.EnclosingClass.EnclosingModuleDefinition;
          res += $"  {requiresOrAndSep} " + GetPrefixedString(path[i].Item1.Name + "_", condExpr, currentModuleDef) + "\n";
        }
        for (int j = 0; j < callExpr.Args.Count; j++) {
          res += $"  {requiresOrAndSep} ";
          res += GetPrefixedString(path[i].Item1.Name + "_", callExpr.Args[j], currentModuleDef);
          res += " == ";
          res += path[i + 1].Item1.Name + "_" + path[i + 1].Item1.Formals[j].Name + "\n";
        }
        foreach (var req in callExpr.Function.Req) {
          res += $"  {requiresOrAndSep} " + GetPrefixedString(path[i + 1].Item1.Name + "_", req.E, currentModuleDef) + "\n";
        }
        res += $"  {requiresOrAndSep} " + callExpr.Function.FullDafnyName + "(";
        sep = "";
        foreach (var arg in callExpr.Args) {
          res += sep + GetPrefixedString(path[i].Item1.Name + "_", arg, currentModuleDef);
          sep = ", ";
        }
        res += ")\n";
      }
      if (constraintExpr != null) {
        currentModuleDef = path[0].Item1.EnclosingClass.EnclosingModuleDefinition;
        res += "  requires " + GetPrefixedString(path[0].Item1.Name + "_", constraintExpr, currentModuleDef) + "\n";
      }
      res += "  ensures false\n{}";
      return res;
    }

public string ReplaceFirst(int pos, string text, string search, string replace)
{
  // int pos = text.IndexOf(search);
  if (pos < 0)
  {
    return text;
  }
  return text.Substring(0, pos) + replace + text.Substring(pos + search.Length);
}

    public void PrintExprAndCreateProcessMethodInPlace(Program program, Program proofProg,Method meth, Method unresolvedMeth, string moduleName,ExpressionFinder.ExpressionDepth expr,Expression originalExpr,bool isEns,bool isReq,int cnt, bool includeProof,bool isWeaker, bool vacTest,Function mutationRootFn) {
      bool runOnce = DafnyOptions.O.HoleEvaluatorRunOnce;
      Console.WriteLine("Mutation -> " + $"{cnt}" + ": " + $"{Printer.ExprToString(expr.expr)}");
      String reqOrEns = isReq ? "requires " :  "ensures ";
      Console.WriteLine("Original -> " + $"{cnt}" + ": " + reqOrEns + $"{Printer.ExprToString(originalExpr)}");
      var funcName = meth.Name;

      string lemmaForExprValidityString = ""; // remove validityCheck
      string basePredicateString = "";
      string isSameLemma = "";
      string isStrongerLemma = "";
      string istWeakerLemma = "";
      string mutationBaseString = ""; 
      string methodMutatedPred = "";
      string methodPred = "";
      string isVacTest = "";


      var paramsAndBodies = GetExtraOldParams(meth,null,null,null); //FIX

      if (isWeaker)
      {
        istWeakerLemma = GetIsWeakerMethodInPlace(meth,MutationsPaths[0], null, null,isReq);
        methodPred = GetIsBasePredMethodInPlace(meth,MutationsPaths[0], null, null,isReq);
        methodMutatedPred = GetIsMutatedPredMethodInPlace(meth,MutationsPaths[0], null, null,isReq,originalExpr,expr.expr);
      }
      // unresolvedMeth.Body = originalExpr;
        //       if(isReq){
        //   foreach (AttributedExpression e in unresolvedMeth.Req)
        //   {
        //     Expression ee = e.E;
        //     //update requires to match "Old" 
        //     string reqExprStr = Printer.ExprToString(ee);
        //     if(reqExprStr == Printer.ExprToString(originalExpr))
        //     {
        //       e.E = expr.expr;
        //     }
        //   }
        // }else{
        //   foreach (AttributedExpression e in unresolvedMeth.Ens)
        //   {
        //      Expression ee = e.E;
        //      string ensExprStr = Printer.ExprToString(ee);
        //     if(ensExprStr == Printer.ExprToString(originalExpr))
        //     {
        //       e.E = expr.expr;
        //     }
        //   }
        // }

      int lemmaForExprValidityPosition = 0;
      int lemmaForExprValidityStartPosition = 0;
      int basePredicatePosition = 0;
      int basePredicateStartPosition = 0;
      var workingDir = $"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}/{meth.Name}_Pred_{cnt}";
//       if (tasksList == null)
//       {
      string code = "";
      string proofCode = "";
      using (var wr = new System.IO.StringWriter()) {
        var pr = new Printer(wr, DafnyOptions.PrintModes.NoIncludes);
        pr.UniqueStringBeforeUnderscore = UnderscoreStr;
        //apply mutation


      var includesList = "";
      foreach (var q in program.DefaultModuleDef.Includes)
      {
        // Console.WriteLine(includeParser.Normalized(q.IncludedFilename));
        // includesList += "include \"" +includeParser.Normalized(q.IncludedFilename) + "\"\n";
        includesList += "include \"" +includeParser.NormalizedTo(program.FullName,q.IncludedFilename) + "\"\n";

      }
//             // Console.WriteLine("--------------\n");

          pr.PrintProgram(program, false);
          // Console.WriteLine("----\n" + Printer.ModuleDefinitionToString(program.DefaultModuleDef,DafnyOptions.PrintModes.Everything));
          // pr.PrintModuleDefinition(program.DefaultModuleDef, program.DefaultModuleDef.VisibilityScope, 0, null, null);
          code = $"// #{cnt}\n";
          code += $"// {Printer.ExprToString(expr.expr)}\n" + includesList + Printer.ToStringWithoutNewline(wr) + "\n\n";
          
          //apply mutation string b/c these are readonly
          var targetIndex = 0;
          if(meth is Lemma)
          {
            targetIndex = code.IndexOf("lemma " + meth.Name);
            if (targetIndex < 0){
              targetIndex = code.IndexOf("} " + meth.Name); 
              targetIndex = code.LastIndexOf("lemma",targetIndex);
            }
            
          }else{
            targetIndex = code.IndexOf("method " + meth.Name);
            if (targetIndex < 0){
              targetIndex = code.IndexOf("} " + meth.Name); 
              targetIndex = code.LastIndexOf("method",targetIndex);
            }
          }
          if(isReq)
          {
           code = ReplaceFirst(code.IndexOf("requires " +Printer.ExprToString(originalExpr),targetIndex),code,"requires " +Printer.ExprToString(originalExpr),"requires " +Printer.ExprToString(expr.expr));
          // code = code.Replace("requires " +Printer.ExprToString(originalExpr),"requires " +Printer.ExprToString(expr.expr));
          }else{
            code = ReplaceFirst(code.IndexOf("ensures " +Printer.ExprToString(originalExpr),targetIndex),code,"ensures " +Printer.ExprToString(originalExpr),"ensures " +Printer.ExprToString(expr.expr));

            // code = code.Replace("ensures " +Printer.ExprToString(originalExpr),"ensures " +Printer.ExprToString(expr.expr));
          }
          if(isWeaker){
            
            code = code.Insert(targetIndex-1,istWeakerLemma+"\n" + methodPred + "\n" + methodMutatedPred + "\n");
          }
          if(vacTest) //just inline "ensures false" 
          {
            methodMutatedPred = GetIsMutatedPredMethodInPlace(meth,MutationsPaths[0], null, null,isReq,originalExpr,expr.expr);
            isVacTest = GetIsSimpleVacTest(meth,MutationsPaths[0], null, null,isReq);
            // var targetIndex = code.IndexOf("method " + meth.Name);
            // if (targetIndex < 0){
            //   targetIndex = code.IndexOf("} " + meth.Name); 
            //   targetIndex = code.LastIndexOf("method",targetIndex);
            // }
            code = code.Insert(targetIndex-1,isVacTest + "\n" + methodMutatedPred + "\n");
          }
//           // if((vacTest && includeProof)){
//           //   int lemmaLoc = code.IndexOf("lemma " +lemma.Name);
//           //   if (lemmaLoc == -1)
//           //   {
//           //     lemmaLoc = code.IndexOf(lemma.Name+"(");
//           //   }
//           //   int lemmaLocEns = code.IndexOf("{",lemmaLoc);
//           //   // Console.WriteLine("here = " + lemmaLocEns);
//           //   code = code.Insert(lemmaLocEns-1,"ensures false;\n");
//           // }

//             if((vacTest)){
//             string revisedVac = getVacuityLemmaRevised(func,Paths[0], null, null,false);
//             if(func.WhatKind == "predicate"){
//               fnIndex = code.IndexOf("predicate " + funcName);
//             }else{
//               fnIndex = code.IndexOf("function " + funcName);
//             }
//             code = code.Insert(fnIndex-1,revisedVac+"\n");
//             // int lemmaLoc = code.IndexOf("lemma " +lemma.Name);
//             // int lemmaLocEns = code.IndexOf("{",lemmaLoc);
//             // // Console.WriteLine("here = " + lemmaLocEns);
//             // code = code.Insert(lemmaLocEns-1,"ensures false;\n");
//           }
          
//           // fnIndex = code.IndexOf("predicate " + funcName);
//           // code = code.Insert(fnIndex-1,isStrongerLemma+"\n");


//           // lemmaForExprValidityStartPosition = code.Count(f => f == '\n') + 1;
//           // code += lemmaForExprValidityString + "\n";
//           // lemmaForExprValidityPosition = code.Count(f => f == '\n');

//           // basePredicateStartPosition = code.Count(f => f == '\n') + 1;
//           // code += basePredicateString + "\n";
//           // basePredicatePosition = code.Count(f => f == '\n');

//           // Console.WriteLine(code.IndexOf("lemma isSame_"+funcName));
          if (DafnyOptions.O.HoleEvaluatorCreateAuxFiles){
            if(isWeaker)
            {
              File.WriteAllTextAsync($"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}{funcName}_weaker_{cnt}.dfy", code);
            }else if (vacTest){
              File.WriteAllTextAsync($"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}{funcName}_vac_{cnt}.dfy", code);
            }else{
                File.WriteAllTextAsync($"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}{funcName}_full_{cnt}.dfy", code);

            }
          }
        }
        string env = DafnyOptions.O.Environment.Remove(0, 22);
        var argList = env.Split(' ');
        List<string> args = new List<string>();

        foreach (var arg in argList) {
          if (!arg.EndsWith(".dfy") && !arg.StartsWith("/holeEval") && arg.StartsWith("/")&& !arg.StartsWith("/proofName") && !arg.StartsWith("/mutationsFromParams")  && !arg.StartsWith("/inPlaceMutation") ) {
            args.Add(arg);
///mutationsFromParams
          }
        }
         if(isWeaker){
          args.Add("/proc:*isAtLeastAsWeak*");
         }else if(vacTest)
         {
          args.Add("/proc:*isVac*");
         }
         else if(includeProof && moduleName == null){
          // args.Add("/proc:*" + meth.Name +"*");
         }

        var changingFilePath = includeParser.Normalized(unresolvedMeth.BodyStartTok.Filename);
        var constraintFuncChangingFilePath = includeParser.Normalized(unresolvedMeth.BodyStartTok.Filename);
//                   // Console.WriteLine("hereerere 3 " + changingFilePath + " :: " + constraintFuncChangingFilePath);
//                   foreach (var p in changingFilePath.Split("/"))
//                   {
//                     // Console.WriteLine(p);
//                   }

        var remoteFolderPath = dafnyVerifier.DuplicateAllFiles(cnt, changingFilePath);

//         // var remoteFolderPath = dafnyVerifier.DuplicateAllFiles(cnt, changingFilePath.Split("/").Last());
//         // Console.WriteLine("Remote = " + remoteFolderPath);
        args.Add("/compile:0");
//       //  List<ProofEvaluator.ExprStmtUnion> exprStmtList = new List<ProofEvaluator.ExprStmtUnion>();
//       //   dafnyVerifier.runDafnyProofCheck(code,args,exprStmtList,0);
//       // Console.WriteLine("code = " + code);
        dafnyVerifier.runDafny(code, args,
            expr, cnt, lemmaForExprValidityPosition, lemmaForExprValidityStartPosition,$"{remoteFolderPath.Path}/{constraintFuncChangingFilePath}");
       
      }
      // else
      // {
      // }
    // }



    public static string GetFullModuleName(ModuleDefinition moduleDef) {
      if (moduleDef.Name == "_module") {
        return "";
      } else if (moduleDef.EnclosingModule.Name == "_module") {
        return moduleDef.Name;
      } else {
        return GetFullModuleName(moduleDef.EnclosingModule) + "." + moduleDef.Name;
      }
    }

    public static string GetFullLemmaNameString(ModuleDefinition moduleDef, string name) {
      if (moduleDef is null) {
        return name;
      }
      foreach (var decl in ModuleDefinition.AllFunctions(moduleDef.TopLevelDecls)) {
        if (decl.ToString() == name) {
          var moduleName = GetFullModuleName(moduleDef);
          return (moduleName == "") ? name : (moduleName + "." + name);
        }
      }
      foreach (var imp in ModuleDefinition.AllDeclarationsAndNonNullTypeDecls(moduleDef.TopLevelDecls)) {
        if (imp is ModuleDecl) {
          var result = GetFullLemmaNameString((imp as ModuleDecl).Signature.ModuleDef, name);
          if (result != "") {
            return result;
          }
        }
      }
      // couldn't find the type definition here, so we should search the parent
      return "";
    }


    public static Tuple<string, string> GetFunctionParamListSpec(Function func, string namePrefix = "") {
      var funcName = func.FullDafnyName;
      string parameterNameTypes = "";
      string paramNames = "";
      var sep = "";
      foreach (var param in func.Formals) {
        parameterNameTypes += sep + namePrefix + param.Name + ":" + Printer.GetFullTypeString(func.EnclosingClass.EnclosingModuleDefinition, param.Type, new HashSet<ModuleDefinition>(),true);
            // parameterNameTypes += sep + namePrefix + param.Name + ":" + Printer.GetFullTypeString(func.EnclosingClass.EnclosingModuleDefinition, param.Type, new HashSet<ModuleDefinition>());
        paramNames += sep + namePrefix + param.Name;
        sep = ", ";
      }
      return new Tuple<string, string>(paramNames, parameterNameTypes);
    }

        public static Tuple<string, string> GetMethodParamListSpec(Method meth, string namePrefix = "") {
      var methName = meth.FullDafnyName;
      string parameterNameTypes = "";
      string paramNames = "";
      var sep = "";
      foreach (var param in meth.Ins) {
        parameterNameTypes += sep + namePrefix + param.Name + ":" + Printer.GetFullTypeString(meth.EnclosingClass.EnclosingModuleDefinition, param.Type, new HashSet<ModuleDefinition>(),true);
            // parameterNameTypes += sep + namePrefix + param.Name + ":" + Printer.GetFullTypeString(func.EnclosingClass.EnclosingModuleDefinition, param.Type, new HashSet<ModuleDefinition>());
        paramNames += sep + namePrefix + param.Name;
        sep = ", ";
      }
      return new Tuple<string, string>(paramNames, parameterNameTypes);
    }

    public static Tuple<string, string> GetFunctionParamList(Function func, string namePrefix = "") {
      var funcName = func.FullDafnyName;
      string parameterNameTypes = "";
      string paramNames = "";
      var sep = "";
      foreach (var param in func.Formals) {
        // parameterNameTypes += sep + namePrefix + param.Name + ":" + Printer.GetFullTypeString(func.EnclosingClass.EnclosingModuleDefinition, param.Type, new HashSet<ModuleDefinition>(),true);
            parameterNameTypes += sep + namePrefix + param.Name + ":" + Printer.GetFullTypeString(func.EnclosingClass.EnclosingModuleDefinition, param.Type, new HashSet<ModuleDefinition>());
        paramNames += sep + namePrefix + param.Name;
        sep = ", ";
      }
      return new Tuple<string, string>(paramNames, parameterNameTypes);
    }

    public static Function GetFunction(Program program, string funcName) {
      foreach (var kvp in program.ModuleSigs) {
        foreach (var topLevelDecl in ModuleDefinition.AllFunctions(kvp.Value.ModuleDef.TopLevelDecls)) {
          if (topLevelDecl.FullDafnyName == funcName) {
            return topLevelDecl;
          }
        }
      }
      return null;
    }

    public static Function GetFunctionFromModuleDef(ModuleDefinition moduleDef, string funcName) {
      foreach (var topLevelDecl in moduleDef.TopLevelDecls) {
        if (topLevelDecl is ClassDecl) {
          var cd = topLevelDecl as ClassDecl;
          foreach (var member in cd.Members) {
            if ($"{cd.FullDafnyName}.{member.Name}" == funcName) {
              return member as Function;
            }
          }
        }
        if(topLevelDecl is DatatypeDecl)
        {
          var cd = topLevelDecl as DatatypeDecl;
          foreach (var member in cd.Members) {
            if ($"{cd.FullDafnyName}.{member.Name}" == funcName) {
              return member as Function;
            }
          }
        }
      }
      return null;
    }
    public static Method GetMethodFromModuleDef(ModuleDefinition moduleDef, string methName) {
      foreach (var topLevelDecl in moduleDef.TopLevelDecls) {
        if (topLevelDecl is ClassDecl) {
          var cd = topLevelDecl as ClassDecl;
          foreach (var member in cd.Members) {
            if ($"{cd.FullDafnyName}.{member.Name}" == methName) {
              return member as Method;
            }
          }
        }
        if(topLevelDecl is DatatypeDecl)
        {
          var cd = topLevelDecl as DatatypeDecl;
          foreach (var member in cd.Members) {
            if ($"{cd.FullDafnyName}.{member.Name}" == methName) {
              return member as Method;
            }
          }
        }
      }
      return null;
    }

    public static Function GetFunctionFromUnresolved(Program program, string funcName) {
      int index = funcName.IndexOf('.');
      string moduleName = funcName.Remove(index);
      foreach (var topLevelDecl in program.DefaultModuleDef.TopLevelDecls) {
        if (topLevelDecl.FullDafnyName == moduleName) {
          var lmd = topLevelDecl as LiteralModuleDecl;
          var func = GetFunctionFromModuleDef(lmd.ModuleDef, funcName);
          if (func != null) {
            return func;
          }
        }
      }
      return null;
    }

    public static Method GetMethodFromUnresolved(Program program, string methodName) {
      int index = methodName.IndexOf('.');
      string moduleName = methodName.Remove(index);
      foreach (var topLevelDecl in program.DefaultModuleDef.TopLevelDecls) {
        if (topLevelDecl.FullDafnyName == moduleName) {
          var lmd = topLevelDecl as LiteralModuleDecl;
          var func = GetMethodFromModuleDef(lmd.ModuleDef, methodName);
          if (func != null) {
            return func;
          }
        }
      }
      return null;
    }

    public void DuplicateAllFiles(Program program, string workingDir, int cnt) {
      if (System.IO.Directory.Exists(workingDir)) {
        System.IO.Directory.Delete(workingDir, true);
      }
      System.IO.Directory.CreateDirectory(workingDir);
      var samples = new List<string>();
      samples.Add(includeParser.Normalized(program.FullName));
      System.IO.Directory.CreateDirectory(Path.GetDirectoryName($"{workingDir}/{samples[0]}"));
      File.Copy(program.FullName, $"{workingDir}/{samples[0]}", true);
      foreach (var file in program.DefaultModuleDef.Includes) {
        samples.Add(includeParser.Normalized(file.CanonicalPath));
      }
      for (int i = 1; i < samples.Count; i++) {
        System.IO.Directory.CreateDirectory(Path.GetDirectoryName($"{workingDir}/{samples[i]}"));
        File.Copy(program.DefaultModuleDef.Includes[i - 1].CanonicalPath, $"{workingDir}/{samples[i]}", true);
      }
    }


    private Function workingFunc = null;
    private Function workingConstraintFunc = null;
    private string[] workingFuncCode;
    private string constraintFuncCode = "";
    private int constraintFuncLineCount = 0;
    private List<string> mergedCode = new List<string>();

  }
}