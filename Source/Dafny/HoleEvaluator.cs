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
  public enum Result {
    Unknown = 0,
    CorrectProof = 1,
    CorrectProofByTimeout = 2,
    IncorrectProof = 3,
    FalsePredicate = 4,
    InvalidExpr = 5
  }
  public class HoleEvaluator {
    private string UnderscoreStr = "";
    private static Random random = new Random();

    public static string RandomString(int length) {
      const string chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";
      return new string(Enumerable.Repeat(chars, length)
          .Select(s => s[random.Next(s.Length)]).ToArray());
    }
    private List<Expression> availableExpressions = new List<Expression>();
    private List<BitArray> bitArrayList = new List<BitArray>();

    private bool IsGoodResult(Result result) {
      return (result == Result.CorrectProof ||
              result == Result.CorrectProofByTimeout ||
              result == Result.IncorrectProof ||
              result == Result.Unknown);
    }
    private Dictionary<int, Result> combinationResults = new Dictionary<int, Result>();
    private Dictionary<int, int> negateOfExpressionIndex = new Dictionary<int, int>();
    private HashSet<string> currCombinations = new HashSet<string>();
    private Dictionary<string, int> bitArrayStringToIndex = new Dictionary<string, int>();
    private DafnyExecutor dafnyMainExecutor = new DafnyExecutor();
    private DafnyExecutor dafnyImpliesExecutor = new DafnyExecutor();

    private string ToBitString(BitArray bits, bool skipZero) {
      var sb = new StringBuilder();

      for (int i = skipZero ? 1 : 0; i < bits.Count; i++) {
        char c = bits[i] ? '1' : '0';
        sb.Append(c);
      }

      return sb.ToString();
    }

    public static int validityLemmaNameStartCol = 0;

    private void UpdateCombinationResult(int index) {
      var p = dafnyMainExecutor.dafnyProcesses[index];
      var fileName = dafnyMainExecutor.inputFileName[p];
      var position = dafnyMainExecutor.processToPostConditionPosition[p];
      var lemmaStartPosition = dafnyMainExecutor.processToLemmaStartPosition[p];
      var expectedOutput =
        $"/tmp/{fileName}.dfy({position},0): Error: A postcondition might not hold on this return path.";
      var expectedInconclusiveOutputStart = 
        $"/tmp/{fileName}.dfy({lemmaStartPosition},{validityLemmaNameStartCol}): Verification inconclusive";
      var output = dafnyMainExecutor.dafnyOutput[p];
      // Console.WriteLine($"{index} => {output}");
      // Console.WriteLine($"{output.EndsWith("0 errors\n")} {output.EndsWith($"resolution/type errors detected in {fileName}.dfy\n")}");
      // Console.WriteLine($"----------------------------------------------------------------");
      var res = DafnyExecutor.IsCorrectOutput(output, expectedOutput, expectedInconclusiveOutputStart);
      if (res != Result.IncorrectProof) {
        // correctExpressions.Add(dafnyMainExecutor.processToExpr[p]);
        // Console.WriteLine(output);
        combinationResults[index] = res;
        // Console.WriteLine(p.StartInfo.Arguments);
        Console.WriteLine(Printer.ExprToString(dafnyMainExecutor.processToExpr[p]));
      } else if (output.EndsWith("0 errors\n")) {
        combinationResults[index] = Result.FalsePredicate;
      } else if (output.EndsWith($"resolution/type errors detected in {fileName}.dfy\n")) {
        combinationResults[index] = Result.InvalidExpr;
      } else {
        combinationResults[index] = Result.IncorrectProof;
      }
    }

    public void Increment(ref BitArray bArray) {
      for (int i = 0; i < bArray.Count; i++) {
        bool previous = bArray[i];
        bArray[i] = !previous;
        if (!previous) {
          // Found a clear bit - now that we've set it, we're done
          return;
        }
      }
    }

    public bool IsGoodExprCombinationToExecute(int indexI, int indexJ) {
      Contract.Requires(indexI >= 0 && indexI < availableExpressions.Count);
      Contract.Requires(indexJ >= 0 && indexJ < availableExpressions.Count);
      if ((!IsGoodResult(combinationResults[indexI])) ||
          (!IsGoodResult(combinationResults[indexJ]))) {
        return false;
      }
      BitArray combinedBitArray = new BitArray(bitArrayList[indexI]);
      combinedBitArray.Or(bitArrayList[indexJ]);

      // Check if the combination is same as input combinations or not
      if (combinedBitArray.Equals(bitArrayList[indexI]) || combinedBitArray.Equals(bitArrayList[indexJ])) {
        return false;
      }
      // Check if this combination has been already executed or not
      if (currCombinations.Contains(ToBitString(combinedBitArray, true))) {
        return false;
      }
      // Check if negate of an expression also exists in this expr combination or not.
      List<int> enabledExprIndexes = new List<int>();
      for (int i = 0; i < combinedBitArray.Count; i++) {
        if (combinedBitArray[i]) {
          enabledExprIndexes.Add(i);
          if (negateOfExpressionIndex.ContainsKey(i)) {
            var negateIndex = negateOfExpressionIndex[i];
            if (combinedBitArray[negateIndex])
              return false;
          }
        }
      }
      BitArray countBitArray = new BitArray(enabledExprIndexes.Count, false);
      countBitArray[0] = true;
      BitArray zeroBitArray = new BitArray(enabledExprIndexes.Count, false);
      while (ToBitString(countBitArray, false) != ToBitString(zeroBitArray, false)) {
        BitArray subsetBitArray = new BitArray(combinedBitArray.Count, false);
        for (int i = 0; i < enabledExprIndexes.Count; i++) {
          subsetBitArray[enabledExprIndexes[i]] = countBitArray[i];
        }
        string subsetString = ToBitString(subsetBitArray, true);
        // Console.WriteLine($"{indexI} {indexJ} {subsetString}");
        // Console.WriteLine($"{ToBitString(countBitArray)} {ToBitString(zeroBitArray)} {countBitArray.Equals(zeroBitArray)}");
        if (bitArrayStringToIndex.ContainsKey(subsetString)) {
          int index = bitArrayStringToIndex[subsetString];
          if (!IsGoodResult(combinationResults[index]))
            return false;
        }
        Increment(ref countBitArray);
      }
      return true;
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

    public static DirectedCallGraph<Function, FunctionCallExpr, Expression> GetCallGraph(Function baseFunc) {
      Contract.Requires(baseFunc != null);
      DirectedCallGraph<Function, FunctionCallExpr, Expression> G = new DirectedCallGraph<Function, FunctionCallExpr, Expression>();
      // Tuple of SubExpression that is going to be parsed, pre-condition to reach this SubExpression, containing Function
      Queue<Tuple<Expression, Expression, Function>> queue = new Queue<Tuple<Expression, Expression, Function>>();
      queue.Enqueue(new Tuple<Expression, Expression, Function>(baseFunc.Body, null, baseFunc));
      G.AddVertex(baseFunc);
      // HashSet<string> keys = new HashSet<string>();
      // keys.Add(Printer.ExprToString(baseF.Body) + ":" + baseF.Body);
      // TODO: Check an example in which a function is called in another function with two different pre-conditions
      while (queue.Count > 0) {
        Tuple<Expression, Expression, Function> currExprCondParentTuple = queue.Dequeue();
        if (currExprCondParentTuple.Item1 == null) continue;
        // Console.WriteLine("Processing " + currExprParentTuple.Item1 + ": " + Printer.ExprToString(currExprParentTuple.Item1));
        if (currExprCondParentTuple.Item1 is FunctionCallExpr /*&& (currExpr as FunctionCallExpr).Function.Body != null*/) {
          // if (!keys.Contains(Printer.ExprToString((currExprParentTuple.Item1 as FunctionCallExpr).Function.Body) + ":" + (currExprParentTuple.Item1 as FunctionCallExpr).Function.Body)) {
          // Console.WriteLine("Adding " + (currExprParentTuple.Item1 as FunctionCallExpr).Function.Body + ": " + Printer.ExprToString((currExprParentTuple.Item1 as FunctionCallExpr).Function.Body));
          // Console.WriteLine($"function call: {Printer.ExprToString((currExprCondParentTuple.Item1 as FunctionCallExpr))}");
          // Console.WriteLine($"{currExprCondParentTuple.Item3.Name} -> {(currExprCondParentTuple.Item1 as FunctionCallExpr).Function.Name}");
          // if (currExprCondParentTuple.Item2 != null) {
          //   Console.WriteLine($"condition : {Printer.ExprToString(currExprCondParentTuple.Item2)}");
          // } else {
          //   Console.WriteLine($"condition : null");
          // }
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
          // }
        }
        if (currExprCondParentTuple.Item1 is ITEExpr) {
          // Console.WriteLine($"ite expr here: {Printer.ExprToString(currExprCondParentTuple.Item1)}");
          var iteExpr = currExprCondParentTuple.Item1 as ITEExpr;

          // add Condition
          queue.Enqueue(new Tuple<Expression, Expression, Function>(
            iteExpr.Test, currExprCondParentTuple.Item2, currExprCondParentTuple.Item3));

          // add then path
          var thenCond = currExprCondParentTuple.Item2 != null ?
            Expression.CreateAnd(currExprCondParentTuple.Item2, iteExpr.Test) :
            iteExpr.Test;
          queue.Enqueue(new Tuple<Expression, Expression, Function>(
            iteExpr.Thn, thenCond, currExprCondParentTuple.Item3));

          // add else path
          var elseCond = currExprCondParentTuple.Item2 != null ?
            Expression.CreateAnd(currExprCondParentTuple.Item2,
                                 Expression.CreateNot(iteExpr.Test.tok, iteExpr.Test)) :
            Expression.CreateNot(iteExpr.Test.tok, iteExpr.Test);
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
            var cond = currExprCondParentTuple.Item2 != null ?
              Expression.CreateAnd(currExprCondParentTuple.Item2, new MemberSelectExpr(c.Ctor.tok, matchExpr.Source, c.Ctor.Name)) :
              new MemberSelectExpr(c.Ctor.tok, matchExpr.Source, c.Ctor.Name + "?");
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
              new BoundVar(bv.Tok, currExprCondParentTuple.Item3.Name + "_" + bv.Name, bv.Type)));
          }
          rhss.Add(existsExpr.Term);
          var cond = Expression.CreateLet(existsExpr.BodyStartTok, lhss, rhss,
            Expression.CreateBoolLiteral(existsExpr.BodyStartTok, true), false);

          queue.Enqueue(new Tuple<Expression, Expression, Function>(existsExpr.Term, cond, currExprCondParentTuple.Item3));
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

    public static string GetPrefixedString(string prefix, Expression expr, ModuleDefinition currentModuleDef) {
      using (var wr = new System.IO.StringWriter()) {
        var pr = new Printer(wr);
        pr.Prefix = prefix;
        pr.ModuleForTypes = currentModuleDef;
        pr.PrintExpression(expr, false);
        return wr.ToString();
      }
    }

    public static string GetValidityLemma(List<Tuple<Function, FunctionCallExpr, Expression>> path, ModuleDefinition currentModuleDef) {
      string res = "lemma {:timeLimitMultiplier 2} validityCheck";
      foreach (var nwPair in path) {
        res += "_" + nwPair.Item1.Name;
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
        if (condExpr != null) {
          currentModuleDef = path[i].Item1.EnclosingClass.EnclosingModuleDefinition;
          res += "  requires " + GetPrefixedString(path[i].Item1.Name + "_", condExpr, currentModuleDef) + "\n";
        }
        for (int j = 0; j < callExpr.Args.Count; j++) {
          res += "  requires ";
          res += GetPrefixedString(path[i].Item1.Name + "_", callExpr.Args[j], currentModuleDef);
          res += " == ";
          res += path[i + 1].Item1.Name + "_" + path[i + 1].Item1.Formals[j].Name + "\n";
        }
        foreach (var req in callExpr.Function.Req) {
          res += "  requires " + GetPrefixedString(path[i + 1].Item1.Name + "_", req.E, currentModuleDef) + "\n";
        }
        res += "  requires " + callExpr.Function.FullDafnyName + "(";
        sep = "";
        foreach (var arg in callExpr.Args) {
          res += sep + GetPrefixedString(path[i].Item1.Name + "_", arg, currentModuleDef);
          sep = ", ";
        }
        res += ")\n";
      }
      if (DafnyOptions.O.HoleEvaluatorConstraint != null) {
        res += "  requires " + DafnyOptions.O.HoleEvaluatorConstraint + "\n";
      }
      res += "  ensures false\n{}";
      return res;
    }

    public IEnumerable<Expression> ListConstructors(
      Type ty,
      DatatypeCtor ctor,
      Dictionary<string, List<Expression>> typeToExpressionDict,
      List<Expression> arguments,
      int shouldFillIndex) {
      if (shouldFillIndex == ctor.Formals.Count) {
        List<ActualBinding> bindings = new List<ActualBinding>();
        foreach (var arg in arguments) {
          bindings.Add(new ActualBinding(null, arg));
        }
        var applySuffixExpr = new ApplySuffix(ctor.tok, null, new NameSegment(ctor.tok, ctor.Name, null), bindings);
        applySuffixExpr.Type = ty;
        yield return applySuffixExpr;
        yield break;
      }
      var t = ctor.Formals[shouldFillIndex].Type;
      if (typeToExpressionDict.ContainsKey(t.ToString())) {
        foreach (var expr in typeToExpressionDict[t.ToString()]) {
          arguments.Add(expr);
          foreach (var ans in ListConstructors(ty, ctor, typeToExpressionDict, arguments, shouldFillIndex + 1)) {
            yield return ans;
          }
          arguments.RemoveAt(arguments.Count - 1);
        }
      }
    }

    public List<Expression> GetAllPossibleConstructors(Program program,
      Type ty,
      DatatypeCtor ctor,
      Dictionary<string, List<Expression>> typeToExpressionDict) {
      List<Expression> result = new List<Expression>();
      List<Expression> workingList = new List<Expression>();
      foreach (var expr in ListConstructors(ty, ctor, typeToExpressionDict, workingList, 0)) {
        result.Add(expr);
      }
      return result;
    }

    public bool EvaluateAfterRemoveFileLine(Program program, string removeFileLine, string baseFuncName, int depth) {
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
              return Evaluate(program, topLevelDecl.FullDafnyName, baseFuncName, depth);
            }
          }
        }
      }
      return false;
    }

    public bool Evaluate(Program program, string funcName, string baseFuncName, int depth) {
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
      dafnyMainExecutor.sw = Stopwatch.StartNew();
      // Console.WriteLine($"hole evaluation begins for func {funcName}");
      Function desiredFunction = null;
      var cnt = 0;
      Function topLevelDeclCopy = null;
      desiredFunction = GetFunction(program, funcName);
      if (desiredFunction != null) {
        var expressions = ListArguments(program, desiredFunction);
        var c = 0;
        Dictionary<string, List<Expression>> typeToExpressionDict = new Dictionary<string, List<Expression>>();
        foreach (var expr in expressions) {
          c++;
          var exprString = Printer.ExprToString(expr);
          var typeString = expr.Type.ToString();
          Console.WriteLine($"{c,2} {exprString,-20} {typeString}");
          if (expr.Type == Type.Bool && exprString[exprString.Length - 1] == '?') {
            typeString = "_questionMark_";
          }
          if (typeToExpressionDict.ContainsKey(typeString)) {
            bool containsItem = typeToExpressionDict[typeString].Any(
                 item => Printer.ExprToString(item) == Printer.ExprToString(expr));
            if (!containsItem) {
              typeToExpressionDict[typeString].Add(expr);
            }
          } else {
            var lst = new List<Expression>();
            lst.Add(expr);
            typeToExpressionDict.Add(typeString, lst);
          }
          // AddExpression(program, topLevelDecl, expr);
        }
        Console.WriteLine("");
        foreach (var k in typeToExpressionDict.Keys) {
          foreach (var v in typeToExpressionDict[k]) {
            Console.WriteLine($"{Printer.ExprToString(v),-20} {k}");
          }
        }
        Console.WriteLine("--------------------------------");
        var equalExprToCheck = desiredFunction.Body;
        foreach (var e in desiredFunction.Req) {
          equalExprToCheck = Expression.CreateAnd(equalExprToCheck, e.E);
        }
        Dictionary<string, List<string>> equalExprList = GetEqualExpressionList(equalExprToCheck);
        foreach (var k in equalExprList.Keys) {
          var t = equalExprList[k][0];
          for (int i = 1; i < equalExprList[k].Count; i++) {
            Console.WriteLine(t + " -> " + k + " = " + equalExprList[k][i]);
          }
          for (int i = 1; i < equalExprList[k].Count; i++) {
            for (int j = 0; j < typeToExpressionDict[t].Count; j++) {
              if (Printer.ExprToString(typeToExpressionDict[t][j]) == equalExprList[k][i]) {
                typeToExpressionDict[t].RemoveAt(j);
                break;
              }
            }
          }
        }
        Dictionary<string, List<Expression>> constructorPerTypeDict = new Dictionary<string, List<Expression>>();
        foreach (var k in typeToExpressionDict.Keys) {
          var t = typeToExpressionDict[k][0].Type;
          if (t is UserDefinedType) {
            var udt = t as UserDefinedType;
            var cl = udt.ResolvedClass;
            if (cl is DatatypeDecl) {
              var dt = (DatatypeDecl)cl;
              var subst = Resolver.TypeSubstitutionMap(dt.TypeArgs, udt.TypeArgs);
              constructorPerTypeDict[k] = new List<Expression>();
              // Console.WriteLine($"{variable.Name} is DatatypeDecl");
              foreach (var ctor in dt.Ctors) {
                var cons = GetAllPossibleConstructors(program, t, ctor, typeToExpressionDict);
                constructorPerTypeDict[k].AddRange(cons);
              }
            }
          }
        }
        foreach (var k in constructorPerTypeDict.Keys) {
          typeToExpressionDict[k].AddRange(constructorPerTypeDict[k]);
        }
        Console.WriteLine("--------------------------------");
        var counter = 0;
        foreach (var k in typeToExpressionDict.Keys) {
          foreach (var v in typeToExpressionDict[k]) {
            Console.WriteLine($"{counter} {Printer.ExprToString(v),-60} {k}");
            counter++;
          }
        }
        topLevelDeclCopy = new Function(
          desiredFunction.tok, desiredFunction.Name, desiredFunction.HasStaticKeyword,
          desiredFunction.IsGhost, desiredFunction.TypeArgs, desiredFunction.Formals,
          desiredFunction.Result, desiredFunction.ResultType, desiredFunction.Req,
          desiredFunction.Reads, desiredFunction.Ens, desiredFunction.Decreases,
          desiredFunction.Body, desiredFunction.ByMethodTok, desiredFunction.ByMethodBody,
          desiredFunction.Attributes, desiredFunction.SignatureEllipsis);
        // check equality of each pair of same type expressions
        var trueExpr = Expression.CreateBoolLiteral(desiredFunction.Body.tok, true);
        availableExpressions.Add(trueExpr);
        foreach (var k in typeToExpressionDict.Keys) {
          var values = typeToExpressionDict[k];
          if (k == "_questionMark_") {
            for (int i = 0; i < values.Count; i++) {
              {
                // No change to the type, add as is
                var expr = values[i];
                availableExpressions.Add(expr);
              }
            }
          } else {
            for (int i = 0; i < values.Count; i++) {
              for (int j = i + 1; j < values.Count; j++) {
                if (values[i] is LiteralExpr && values[j] is LiteralExpr) {
                  continue;
                }
                if (values[i] is ApplySuffix && values[j] is ApplySuffix) {
                  continue;
                }
                // Equality
                {
                  var equalityExpr = Expression.CreateEq(values[i], values[j], values[i].Type);
                  equalityExpr.HasCardinality = values[i].HasCardinality | values[j].HasCardinality;
                  availableExpressions.Add(equalityExpr);
                }
                if (values[i] is ApplySuffix || values[j] is ApplySuffix) {
                  continue;
                }
                // Non-Equality
                {
                  var neqExpr = Expression.CreateNot(values[i].tok, Expression.CreateEq(values[i], values[j], values[i].Type));
                  neqExpr.HasCardinality = values[i].HasCardinality | values[j].HasCardinality;
                  availableExpressions.Add(neqExpr);
                  negateOfExpressionIndex[availableExpressions.Count - 1] = availableExpressions.Count - 2;
                  negateOfExpressionIndex[availableExpressions.Count - 2] = availableExpressions.Count - 1;
                }
                if (k == "bool") {
                  continue;
                }

                // Lower than
                {
                  var lowerThanExpr = Expression.CreateLess(values[i], values[j]);
                  lowerThanExpr.HasCardinality = values[i].HasCardinality | values[j].HasCardinality;
                  availableExpressions.Add(lowerThanExpr);
                }
                // Greater Equal = !(Lower than)
                {
                  var geExpr = Expression.CreateNot(values[i].tok, Expression.CreateLess(values[i], values[j]));
                  geExpr.HasCardinality = values[i].HasCardinality | values[j].HasCardinality;
                  availableExpressions.Add(geExpr);
                  negateOfExpressionIndex[availableExpressions.Count - 1] = availableExpressions.Count - 2;
                  negateOfExpressionIndex[availableExpressions.Count - 2] = availableExpressions.Count - 1;
                }
                // Lower Equal
                {
                  var leExpr = Expression.CreateAtMost(values[i], values[j]);
                  leExpr.HasCardinality = values[i].HasCardinality | values[j].HasCardinality;
                  availableExpressions.Add(leExpr);
                }
                // Greater Than = !(Lower equal)
                {
                  var gtExpr = Expression.CreateNot(values[i].tok, Expression.CreateAtMost(values[i], values[j]));
                  gtExpr.HasCardinality = values[i].HasCardinality | values[j].HasCardinality;
                  availableExpressions.Add(gtExpr);
                  negateOfExpressionIndex[availableExpressions.Count - 1] = availableExpressions.Count - 2;
                  negateOfExpressionIndex[availableExpressions.Count - 2] = availableExpressions.Count - 1;
                }
              }
            }
          }
        }
      } else {
        Console.WriteLine($"{funcName} was not found!");
        return false;
      }
      for (int i = 0; i < availableExpressions.Count; i++) {
        PrintExprAndCreateProcess(program, desiredFunction, availableExpressions[i], i);
        desiredFunction.Body = topLevelDeclCopy.Body;
        BitArray bitArray = new BitArray(availableExpressions.Count, false);
        bitArray[i] = true;
        bitArrayList.Add(bitArray);
        if (i == 0) {
          currCombinations.Add(ToBitString(bitArray, false));
          bitArrayStringToIndex[ToBitString(bitArray, false)] = i;
        } else {
          currCombinations.Add(ToBitString(bitArray, true));
          bitArrayStringToIndex[ToBitString(bitArray, true)] = i;
        }
        combinationResults[i] = Result.Unknown;
      }
      dafnyMainExecutor.startAndWaitUntilAllProcessesFinishAndDumpTheirOutputs(runOnce);

      // bool foundCorrectExpr = false;
      for (int i = 0; i < availableExpressions.Count; i++) {
        UpdateCombinationResult(i);
        // foundCorrectExpr |= combinationResults[i] == Result.CorrectProof;
      }

      // for (int i = 0; i < bitArrayList.Count; i++) {
      //   Console.WriteLine(i + " : " +
      //                     Printer.ExprToString(availableExpressions[i]) + " : " +
      //                     combinationResults[i].ToString());
      // }

      // If no correct expression has found, try to look at depth 2
      // TODO: make this configurable
      // if (foundCorrectExpr == false && depth == 1) {
      //   depth = 2;
      // }

      // Until here, we only check depth 1 of expressions.
      // Now we try to check next depths
      int numberOfSingleExpr = availableExpressions.Count;
      int prevDepthExprStartIndex = 0;
      cnt = availableExpressions.Count;
      for (int dd = 2; dd <= depth; dd++) {
        var tmp = availableExpressions.Count;
        for (int i = prevDepthExprStartIndex; i < tmp; i++) {
          for (int j = 0; j < numberOfSingleExpr; j++) {
            if (IsGoodExprCombinationToExecute(i, j)) {
              var exprA = availableExpressions[i];
              var exprB = availableExpressions[j];
              var conjunctExpr = Expression.CreateAnd(exprA, exprB);
              conjunctExpr.HasCardinality = exprA.HasCardinality | exprB.HasCardinality;
              availableExpressions.Add(conjunctExpr);
              BitArray bitArray = new BitArray(bitArrayList[i]);
              bitArray.Or(bitArrayList[j]);
              bitArrayList.Add(bitArray);
              currCombinations.Add(ToBitString(bitArray, true));
              bitArrayStringToIndex[ToBitString(bitArray, true)] = bitArrayList.Count - 1;
              combinationResults[bitArrayList.Count - 1] = Result.Unknown;
              PrintExprAndCreateProcess(program, desiredFunction, conjunctExpr, cnt);
              cnt++;
              desiredFunction.Body = topLevelDeclCopy.Body;
            }
          }
        }
        dafnyMainExecutor.startAndWaitUntilAllProcessesFinishAndDumpTheirOutputs(runOnce);
        for (int i = tmp; i < availableExpressions.Count; i++) {
          UpdateCombinationResult(i);
        }
        prevDepthExprStartIndex = tmp;
      }
      Console.WriteLine($"{dafnyMainExecutor.sw.ElapsedMilliseconds / 1000}:: finish exploring, try to calculate implies graph");
      int correctProofCount = 0;
      int correctProofByTimeoutCount = 0;
      int incorrectProofCount = 0;
      int invalidExprCount = 0;
      int falsePredicateCount = 0;
      for (int i = 0; i < availableExpressions.Count; i++) {
        switch (combinationResults[i]) {
          case Result.InvalidExpr: invalidExprCount++; break;
          case Result.FalsePredicate: falsePredicateCount++; break;
          case Result.CorrectProof: correctProofCount++; break;
          case Result.CorrectProofByTimeout: correctProofByTimeoutCount++; break;
          case Result.IncorrectProof: incorrectProofCount++; break;
          case Result.Unknown: throw new NotSupportedException();
        }
      }
      Console.WriteLine("{0,-15} {1,-15} {2,-15} {3,-15} {4, -25} {5, -15]",
        "InvalidExpr", "IncorrectProof", "FalsePredicate", "CorrectProof", "CorrectProofByTimeout", "Total");
      Console.WriteLine("{0,-15} {1,-15} {2,-15} {3,-15} {4, -25} {5, -15}",
        invalidExprCount, incorrectProofCount, falsePredicateCount, correctProofCount, correctProofByTimeoutCount, availableExpressions.Count);
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
        Console.WriteLine("proof already goes through and no additional conjunction is needed!");
        return true;
      }
      List<int> correctExpressionsIndex = new List<int>();
      for (int i = 0; i < availableExpressions.Count; i++) {
        if (combinationResults[i] == Result.CorrectProof || combinationResults[i] == Result.CorrectProofByTimeout)
          correctExpressionsIndex.Add(i);
      }
      // for (int i = 0; i < correctExpressionsIndex.Count; i++) {
      //   Console.WriteLine($"correct Expr #{correctExpressionsIndex[i],3}: {Printer.ExprToString(availableExpressions[correctExpressionsIndex[i]])}");
      // }
      for (int i = 0; i < correctExpressionsIndex.Count; i++) {
        for (int j = i + 1; j < correctExpressionsIndex.Count; j++) {
          {
            PrintImplies(program, desiredFunction, correctExpressionsIndex[i], correctExpressionsIndex[j]);
            PrintImplies(program, desiredFunction, correctExpressionsIndex[j], correctExpressionsIndex[i]);
          }
        }
      }
      dafnyImpliesExecutor.startAndWaitUntilAllProcessesFinishAndDumpTheirOutputs(true);
      Console.WriteLine($"{dafnyMainExecutor.sw.ElapsedMilliseconds / 1000}:: finish calculating implies, printing the dot graph");
      string graphVizOutput = $"digraph \"{funcName}_implies_graph\" {{\n";
      graphVizOutput += "  // The list of correct expressions\n";
      for (int i = 0; i < correctExpressionsIndex.Count; i++) {
        graphVizOutput += $"  {correctExpressionsIndex[i]} [label=\"{Printer.ExprToString(availableExpressions[correctExpressionsIndex[i]])}\"];\n";
      }
      graphVizOutput += "\n  // The list of edges:\n";
      foreach (var p in dafnyImpliesExecutor.dafnyProcesses) {
        var availableExprAIndex = dafnyImpliesExecutor.processToAvailableExprAIndex[p];
        var availableExprBIndex = dafnyImpliesExecutor.processToAvailableExprBIndex[p];
        // skip connecting all nodes to true
        if (Printer.ExprToString(availableExpressions[availableExprAIndex]) == "true" ||
            Printer.ExprToString(availableExpressions[availableExprBIndex]) == "true")
          continue;
        var output = dafnyImpliesExecutor.dafnyOutput[p];
        if (output.EndsWith("0 errors\n")) {
          Console.WriteLine($"edge from {availableExprAIndex} to {availableExprBIndex}");
          graphVizOutput += $"  {availableExprAIndex} -> {availableExprBIndex};\n";
        }
      }
      graphVizOutput += "}\n";
      File.WriteAllTextAsync($"/tmp/graph_{funcName}_implies.dot", graphVizOutput);
      Console.WriteLine($"{dafnyMainExecutor.sw.ElapsedMilliseconds / 1000}:: end");
      return true;
    }

    public static string GetFullModuleName(ModuleDefinition moduleDef) {
      if (moduleDef.Name == "_module") {
        return "";
      } else if (moduleDef.EnclosingModule.Name == "_module") {
        return moduleDef.Name;
      } else {
        return GetFullModuleName(moduleDef.EnclosingModule) + "." + moduleDef.Name;
      }
    }

    public static string GetFullTypeString(ModuleDefinition moduleDef, Type type) {
      if (moduleDef is null) {
        return type.ToString();
      }
      if (type is UserDefinedType) {
        var udt = type as UserDefinedType;
        if (udt.Name == "nat" || udt.Name == "object?")
          return udt.ToString();
        foreach (var decl in ModuleDefinition.AllTypesWithMembers(moduleDef.TopLevelDecls)) {
          if (decl.ToString() == type.ToString()) {
            var moduleName = GetFullModuleName(moduleDef);
            return (moduleName == "") ? type.ToString() : (moduleName + "." + type.ToString());
          }
        }
        foreach (var imp in ModuleDefinition.AllDeclarationsAndNonNullTypeDecls(moduleDef.TopLevelDecls)) {
          if (imp is ModuleDecl) {
            var result = GetFullTypeString((imp as ModuleDecl).Signature.ModuleDef, type);
            if (result != "") {
              return result;
            }
          }
        }
        // couldn't find the type definition here, so we should search the parent
        return GetFullTypeString(moduleDef.EnclosingModule, type);
      } else if (type is CollectionType) {
        var ct = type as CollectionType;
        var result = ct.CollectionTypeName + "<";
        var sep = "";
        foreach (var typeArg in ct.TypeArgs) {
          result += sep + GetFullTypeString(moduleDef, typeArg);
          sep = ",";
        }
        result += ">";
        return result;
      } else {
        return type.ToString();
      }
    }

    public static Tuple<string, string> GetFunctionParamList(Function func, string namePrefix = "") {
      var funcName = func.FullDafnyName;
      string parameterNameTypes = "";
      string paramNames = "";
      var sep = "";
      foreach (var param in func.Formals) {
        parameterNameTypes += sep + namePrefix + param.Name + ":" + GetFullTypeString(func.EnclosingClass.EnclosingModuleDefinition, param.Type);
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

    public void PrintExprAndCreateProcess(Program program, Function func, Expression expr, int cnt) {
      bool runOnce = DafnyOptions.O.HoleEvaluatorRunOnce;
      Console.WriteLine($"{cnt} {Printer.ExprToString(expr)}");
      string lemmaForExprValidityString = GetValidityLemma(Paths[0], null);

      var funcName = func.FullDafnyName;
      int lemmaForExprValidityPosition = 0;
      int lemmaForExprValidityStartPosition = 0;

      using (var wr = new System.IO.StringWriter()) {
        var pr = new Printer(wr, DafnyOptions.PrintModes.DllEmbed);
        pr.UniqueStringBeforeUnderscore = UnderscoreStr;
        if (expr.HasCardinality) {
          func.Body = Expression.CreateAnd(expr, func.Body);
        } else {
          func.Body = Expression.CreateAnd(func.Body, expr);
        }
        pr.PrintProgram(program, true);
        var code = $"// {Printer.ExprToString(expr)}\n" + Printer.ToStringWithoutNewline(wr) + "\n\n";
        lemmaForExprValidityStartPosition = code.Count(f => f == '\n') + 1;
        code += lemmaForExprValidityString + "\n";
        lemmaForExprValidityPosition = code.Count(f => f == '\n');
        File.WriteAllTextAsync($"/tmp/{funcName}_{cnt}.dfy", code);
        // Console.WriteLine(Printer.ToStringWithoutNewline(wr));
        // Console.WriteLine("");
      }
      string dafnyBinaryPath = System.Reflection.Assembly.GetEntryAssembly().Location;
      dafnyBinaryPath = dafnyBinaryPath.Substring(0, dafnyBinaryPath.Length - 4);
      string env = CommandLineOptions.Clo.Environment.Remove(0, 22);
      var argList = env.Split(' ');
      string args = "";
      foreach (var arg in argList) {
        if (!arg.EndsWith(".dfy") && !arg.StartsWith("/holeEval") && arg.StartsWith("/")) {
          args += arg + " ";
        }
      }
      // Console.WriteLine($"Creating process : ");
      dafnyMainExecutor.createProcessWithOutput(dafnyBinaryPath,
          $"{args} /tmp/{funcName}_{cnt}.dfy " + (runOnce ? "/exitAfterFirstError" : "/proc:Impl*validityCheck*"),
          expr, cnt, lemmaForExprValidityPosition, lemmaForExprValidityStartPosition, $"{funcName}_{cnt}");
      // Printer.PrintFunction(transformedFunction, 0, false);
    }

    public void PrintImplies(Program program, Function func, int availableExprAIndex, int availableExprBIndex) {
      // Console.WriteLine($"print implies {availableExprAIndex} {availableExprBIndex}");
      var funcName = func.FullDafnyName;
      var paramList = GetFunctionParamList(func);
      var parameterNameTypes = paramList.Item2;
      string lemmaForCheckingImpliesString = "lemma checkIfExprAImpliesExprB(";
      lemmaForCheckingImpliesString += parameterNameTypes + ")\n";
      Expression A = availableExpressions[availableExprAIndex];
      Expression B = availableExpressions[availableExprBIndex];
      lemmaForCheckingImpliesString += "  requires " + Printer.ExprToString(A) + "\n";
      lemmaForCheckingImpliesString += "  ensures " + Printer.ExprToString(B) + "\n";
      lemmaForCheckingImpliesString += "{}";

      int lemmaForCheckingImpliesPosition = 0;

      using (var wr = new System.IO.StringWriter()) {
        var pr = new Printer(wr, DafnyOptions.PrintModes.DllEmbed);
        pr.UniqueStringBeforeUnderscore = UnderscoreStr;
        pr.PrintProgram(program, true);
        var code = $"// Implies {Printer.ExprToString(A)} ==> {Printer.ExprToString(B)}\n" + Printer.ToStringWithoutNewline(wr) + "\n\n";
        code += lemmaForCheckingImpliesString + "\n";
        lemmaForCheckingImpliesPosition = code.Count(f => f == '\n');
        File.WriteAllTextAsync($"/tmp/{funcName}_implies_{availableExprAIndex}_{availableExprBIndex}.dfy", code);
      }

      string dafnyBinaryPath = System.Reflection.Assembly.GetEntryAssembly().Location;
      dafnyBinaryPath = dafnyBinaryPath.Substring(0, dafnyBinaryPath.Length - 4);
      string env = CommandLineOptions.Clo.Environment.Remove(0, 22);
      var argList = env.Split(' ');
      string args = "";
      foreach (var arg in argList) {
        if (!arg.EndsWith(".dfy") && !arg.StartsWith("/holeEval") && !arg.StartsWith("/proc:") && args.StartsWith("/")) {
          args += arg + " ";
        }
      }
      dafnyImpliesExecutor.createProcessWithOutput(dafnyBinaryPath,
        $"{args} /tmp/{funcName}_implies_{availableExprAIndex}_{availableExprBIndex}.dfy /proc:Impl*checkIfExprAImpliesExprB*",
        availableExprAIndex, availableExprBIndex, -1, lemmaForCheckingImpliesPosition,
        $"{funcName}_implies_{availableExprAIndex}_{availableExprBIndex}.dfy");
    }

    // public static Function AddExpression(Function func, Expression expr)
    // {
    //   Function result = new Function(func.tok, func.Name, func.HasStaticKeyword, func.IsGhost,
    //   func.TypeArgs, func.Formals, func.Result, func.ResultType,
    //   func.Req, func.Reads, func.Ens, func.Decreases,
    //   Expression.CreateAnd(func.Body, expr), func.ByMethodTok, func.ByMethodBody,
    //   func.Attributes, func.SignatureEllipsis);
    //   return result;
    // }

    public IEnumerable<Expression> ListArguments(Program program, Function func) {
      foreach (var formal in func.Formals) {
        // Console.WriteLine($"\n{formal.Name}\t{formal.Type.ToString()}");
        // Console.WriteLine(formal.Type.NormalizeExpand().IsTopLevelTypeWithMembers);
        // var c = 0;
        var identExpr = Expression.CreateIdentExpr(formal);
        foreach (var expr in TraverseFormal(program, identExpr)) {
          // Console.WriteLine($"{c} {variable.Name,-20}:\t{variable.Type}");
          // c++;
          yield return expr;
        }

      }
    }

    public IEnumerable<Expression> TraverseFormal(Program program, Expression expr) {
      Contract.Requires(expr != null);
      yield return expr;
      var t = expr.Type;
      if (t is BoolType || t is CharType || t is IntType || t is BigOrdinalType ||
          t is RealType || t is BitvectorType || t is CollectionType) {
        if (t is BoolType) {
          var trueLiteralExpr = Expression.CreateBoolLiteral(expr.tok, true);
          yield return trueLiteralExpr;
          // NOTE: No need to add false literal since we also check for non-equality.
        } else if (t is IntType) {
          var zeroLiteralExpr = Expression.CreateIntLiteral(expr.tok, 0);
          yield return zeroLiteralExpr;
          var oneLiteralExpr = Expression.CreateIntLiteral(expr.tok, 1);
          yield return oneLiteralExpr;
        } else if (t is CollectionType) {
          // create cardinality
          var cardinalityExpr = Expression.CreateCardinality(expr, program.BuiltIns);
          yield return cardinalityExpr;
          if (t is SeqType) {
            var zeroLiteralExpr = Expression.CreateIntLiteral(expr.tok, 0);
            var zerothElement = new SeqSelectExpr(expr.tok, true, expr, zeroLiteralExpr, null);
            var st = t as SeqType;
            zerothElement.Type = st.Arg;
            foreach (var e in TraverseFormal(program, zerothElement)) {
              yield return e;
            }
            // create 0th element of the sequence
          }
        }
        // Console.WriteLine("pre-defined variable type");
        yield break;
      }
      var udt = (UserDefinedType)t;
      var cl = udt.ResolvedClass;
      if (cl is OpaqueTypeDecl) {
        var otd = (OpaqueTypeDecl)cl;
        // Console.WriteLine($"{variable.Name} is OpaqueTypeDecl");
        // TODO traverse underlying definition as well.
        throw new NotImplementedException();
      } else if (cl is TypeParameter) {
        var tp = (TypeParameter)cl;
        // Console.WriteLine($"{variable.Name} is TypeParameter");
        // TODO traverse underlying definition as well.
        throw new NotImplementedException();
      } else if (cl is InternalTypeSynonymDecl) {
        var isyn = (InternalTypeSynonymDecl)cl;
        // Console.WriteLine($"{variable.Name} is InternalTypeSynonymDecl");
        // TODO traverse underlying definition as well.
        throw new NotImplementedException();
      } else if (cl is NewtypeDecl) {
        var td = (NewtypeDecl)cl;
        Console.WriteLine($"{Printer.ExprToString(td.Constraint)} {td.Var.Name} {td.BaseType} {td.BaseType is IntType}");
        // TODO possibly figure out other expressions from td.Constraint
        if (td.BaseType is IntType) {
          var zeroLiteralExpr = Expression.CreateIntLiteral(expr.tok, 0);
          zeroLiteralExpr.Type = t;
          // TODO Add the literal for maximum value of this newtype decl.
          yield return zeroLiteralExpr;
          var oneLiteralExpr = Expression.CreateIntLiteral(expr.tok, 1);
          oneLiteralExpr.Type = t;
          yield return oneLiteralExpr;
        } else {
          throw new NotImplementedException();
        }
        // foreach (var v in TraverseType(program, td.BaseType)) {
        //   // var ngv = (Formal)variable;
        //   // var dotVar = new Formal(ngv.tok, ngv.Name + "." + v.Name, v.Type, true, true, null);
        //   Console.WriteLine($"!!!! {v.val}");
        //   var e = new ExprDotName(v, expr, v.val, null);
        //   e.Type = expr.Type;
        //   // Console.WriteLine($"Constructing dot var:{dotVar.Name}");
        //   yield return e;
        // }
      } else if (cl is SubsetTypeDecl) {
        Console.WriteLine($"{Printer.ExprToString(expr)}");
        var td = (SubsetTypeDecl)cl;
        Console.WriteLine($"{Printer.ExprToString(td.Constraint)} {td.Var.Name} {td.Rhs}");
        if (td.Rhs is IntType) {
          var zeroLiteralExpr = Expression.CreateIntLiteral(expr.tok, 0);
          zeroLiteralExpr.Type = t;
          yield return zeroLiteralExpr;
          var oneLiteralExpr = Expression.CreateIntLiteral(expr.tok, 1);
          oneLiteralExpr.Type = t;
          yield return oneLiteralExpr;

        }
        // Console.WriteLine($"{variable.Name} is SubsetTypeDecl");
      } else if (cl is ClassDecl) {
        // Console.WriteLine($"{variable.Name} is ClassDecl");
        // TODO traverse underlying definition as well.
        throw new NotImplementedException();
      } else if (cl is DatatypeDecl) {
        var dt = (DatatypeDecl)cl;
        var subst = Resolver.TypeSubstitutionMap(dt.TypeArgs, udt.TypeArgs);
        // Console.WriteLine($"{variable.Name} is DatatypeDecl");
        foreach (var ctor in dt.Ctors) {
          if (dt.Ctors.Count > 1) {
            var exprDot = new ExprDotName(ctor.tok, expr, ctor.tok.val + "?", null);
            exprDot.Type = Type.Bool;
            yield return exprDot;
          }
          foreach (var formal in ctor.Formals) {
            // Console.WriteLine($"type={formal.Type} => {Resolver.SubstType(formal.Type, subst)}");
            // var convertedFormal = new Formal(formal.tok, formal.Name, 
            //     Resolver.SubstType(formal.Type, subst), formal.InParam, formal.IsGhost,
            //     formal.DefaultValue, formal.IsOld, formal.IsNameOnly, formal.NameForCompilation);
            // var identExpr = Expression.CreateIdentExpr(convertedFormal);
            var exprDot = new ExprDotName(formal.tok, expr, formal.tok.val, null);
            exprDot.Type = Resolver.SubstType(formal.Type, subst);
            foreach (var v in TraverseFormal(program, exprDot)) {
              // Console.WriteLine($"aaa {v.tok.val}");
              // // var ngv = (Formal)variable;
              // // var dotVar = new Formal(ngv.tok, ngv.Name + "." + v.Name, v.Type, true, true, null);
              // // Console.WriteLine($"Constructing dot var:{dotVar.Name}");
              // var e = new ExprDotName(v.tok, expr, v.tok.val, null);
              // e.Type = v.Type;
              yield return v;
            }
            // Console.WriteLine($"aaaa {formal.Name}");
          }
        }
      }
      // var members = expr.Type.NormalizeExpand().AsTopLevelTypeWithMembers;
      // foreach(var mem in members.Members)
      // {
      //   Console.WriteLine(mem);
      // }
      // if (expr.SubExpressions != null)
      // {
      // foreach (var subexpr in expr.SubExpressions)
      // {
      //   TraverseFormal(subexpr);
      // }
      // }
    }

    public IEnumerable<IToken> TraverseType(Program program, Type t) {
      Console.WriteLine(t.ToString());
      if (t is BoolType || t is CharType || t is IntType || t is BigOrdinalType ||
          t is RealType || t is BitvectorType || t is CollectionType) {
        Console.WriteLine("pre-defined type");
        yield break;
      }
      var udt = (UserDefinedType)t;
      var cl = udt.ResolvedClass;
      if (cl is OpaqueTypeDecl) {
        var otd = (OpaqueTypeDecl)cl;
        // Console.WriteLine($"{t.ToString()} is OpaqueTypeDecl");
        // TODO traverse underlying definition as well.
      } else if (cl is TypeParameter) {
        var tp = (TypeParameter)cl;
        // Console.WriteLine($"{t.ToString()} is TypeParameter");
        // TODO traverse underlying definition as well.
      } else if (cl is InternalTypeSynonymDecl) {
        var isyn = (InternalTypeSynonymDecl)cl;
        // Console.WriteLine($"{t.ToString()} is InternalTypeSynonymDecl");
        // TODO traverse underlying definition as well.
      } else if (cl is NewtypeDecl) {
        var td = (NewtypeDecl)cl;
        Console.WriteLine($"{t.ToString()} is NewtypeDecl");
        foreach (var v in TraverseType(program, td.BaseType)) {
          yield return v;
        }
      } else if (cl is SubsetTypeDecl) {
        var td = (SubsetTypeDecl)cl;
        // Console.WriteLine($"{t.ToString()} is SubsetTypeDecl");
        // TODO traverse underlying definition as well.
      } else if (cl is ClassDecl) {
        // Console.WriteLine($"{t.ToString()} is ClassDecl");
        // TODO traverse underlying definition as well.
      } else if (cl is DatatypeDecl) {
        var dt = (DatatypeDecl)cl;
        // Console.WriteLine($"{t.ToString()} is DatatypeDecl");
        // TODO traverse underlying definition as well.
      } else {
        // Console.WriteLine($"{t.ToString()} is unknown");
      }
      // var members = expr.Type.NormalizeExpand().AsTopLevelTypeWithMembers;
      // foreach(var mem in members.Members)
      // {
      //   Console.WriteLine(mem);
      // }
      // if (expr.SubExpressions != null)
      // {
      // foreach (var subexpr in expr.SubExpressions)
      // {
      //   TraverseFormal(subexpr);
      // }
      // }
    }


  }
}