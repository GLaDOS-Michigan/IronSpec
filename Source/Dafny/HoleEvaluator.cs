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

  public class HoleEvaluator {
    private string UnderscoreStr = "";
    private static Random random = new Random();

    public static string RandomString(int length) {
      const string chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789";
      return new string(Enumerable.Repeat(chars, length)
          .Select(s => s[random.Next(s.Length)]).ToArray());
    }
    private List<Expression> availableExpressions = new List<Expression>();
    private List<BitArray> bitArrayList = new List<BitArray>();
    enum Result {
      Unknown = 0,
      CorrectProof = 1,
      IncorrectProof = 2,
      FalsePredicate = 3,
      InvalidExpr = 4
    }
    private bool IsGoodResult(Result result) {
      return (result == Result.CorrectProof ||
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

    private void UpdateCombinationResult(int index) {
      var p = dafnyMainExecutor.dafnyProcesses[index];
      var fileName = dafnyMainExecutor.inputFileName[p];
      var position = dafnyMainExecutor.processToLemmaPosition[p];
      var expectedOutput =
        $"/tmp/{fileName}.dfy({position + 3},0): Error: A postcondition might not hold on this return path.";
      var output = dafnyMainExecutor.dafnyOutput[p];
      // Console.WriteLine($"{index} => {output}");
      // Console.WriteLine($"{output.EndsWith("0 errors\n")} {output.EndsWith($"resolution/type errors detected in {fileName}.dfy\n")}");
      // Console.WriteLine($"----------------------------------------------------------------");
      if (DafnyExecutor.IsCorrectOutput(output, expectedOutput)) {
        // correctExpressions.Add(dafnyMainExecutor.processToExpr[p]);
        // Console.WriteLine(output);
        combinationResults[index] = Result.CorrectProof;
        Console.WriteLine(p.StartInfo.Arguments);
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

    public class Graph<T> {
      public Graph() { }
      public Graph(IEnumerable<T> vertices, IEnumerable<Tuple<T, T>> edges) {
        foreach (var vertex in vertices)
          AddVertex(vertex);

        foreach (var edge in edges)
          AddEdge(edge);
      }

      public Dictionary<T, HashSet<T>> AdjacencyList { get; } = new Dictionary<T, HashSet<T>>();

      public void AddVertex(T vertex) {
        AdjacencyList[vertex] = new HashSet<T>();
      }

      public void AddEdge(Tuple<T, T> edge) {
        if (AdjacencyList.ContainsKey(edge.Item1) && AdjacencyList.ContainsKey(edge.Item2)) {
          AdjacencyList[edge.Item1].Add(edge.Item2);
          AdjacencyList[edge.Item2].Add(edge.Item1);
        }
      }
    }

    public HashSet<T> DFS<T>(Graph<T> graph, T start) {
      var visited = new HashSet<T>();

      if (!graph.AdjacencyList.ContainsKey(start))
        return visited;

      var stack = new Stack<T>();
      stack.Push(start);

      while (stack.Count > 0) {
        var vertex = stack.Pop();

        if (visited.Contains(vertex))
          continue;

        visited.Add(vertex);

        foreach (var neighbor in graph.AdjacencyList[vertex])
          if (!visited.Contains(neighbor))
            stack.Push(neighbor);
      }

      return visited;
    }

    public Dictionary<string, List<string>> GetEqualExpressionList(Expression expr) {
      // The first element of each value's list in the result is the type of list
      Dictionary<string, List<string>> result = new Dictionary<string, List<string>>();
      Graph<string> G = new Graph<string>();
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
          HashSet<string> newVisits = DFS<string>(G, e0);
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

    public bool Evaluate(Program program, string funcName, int depth) {
      UnderscoreStr = RandomString(8);
      dafnyMainExecutor.sw = Stopwatch.StartNew();
      // Console.WriteLine($"hole evaluation begins for func {funcName}");
      var foundDesiredFunction = false;
      Function desiredFunction = null;
      var cnt = 0;
      Function topLevelDeclCopy = null;
      foreach (var kvp in program.ModuleSigs) {
        // iterate over all functions / predicates (this doesn't include lemmas)
        foreach (var topLevelDecl in ModuleDefinition.AllFunctions(kvp.Value.ModuleDef.TopLevelDecls)) {
          if (topLevelDecl.FullDafnyName == funcName) {
            Console.WriteLine("Found desired function.");
            foundDesiredFunction = true;
            desiredFunction = topLevelDecl;
            var expressions = ListArguments(program, topLevelDecl);
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
            Dictionary<string, List<string>> equalExprList = GetEqualExpressionList(topLevelDecl.Body);
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
            Console.WriteLine("--------------------------------");
            foreach (var k in typeToExpressionDict.Keys) {
              foreach (var v in typeToExpressionDict[k]) {
                Console.WriteLine($"{Printer.ExprToString(v),-20} {k}");
              }
            }
            topLevelDeclCopy = new Function(
              topLevelDecl.tok, topLevelDecl.Name, topLevelDecl.HasStaticKeyword,
              topLevelDecl.IsGhost, topLevelDecl.TypeArgs, topLevelDecl.Formals,
              topLevelDecl.Result, topLevelDecl.ResultType, topLevelDecl.Req,
              topLevelDecl.Reads, topLevelDecl.Ens, topLevelDecl.Decreases,
              topLevelDecl.Body, topLevelDecl.ByMethodTok, topLevelDecl.ByMethodBody,
              topLevelDecl.Attributes, topLevelDecl.SignatureEllipsis);
            // check equality of each pair of same type expressions
            var trueExpr = Expression.CreateBoolLiteral(topLevelDecl.Body.tok, true);
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
                    // Equality
                    {
                      var equalityExpr = Expression.CreateEq(values[i], values[j], values[i].Type);
                      availableExpressions.Add(equalityExpr);
                    }
                    // Non-Equality
                    {
                      var neqExpr = Expression.CreateNot(values[i].tok, Expression.CreateEq(values[i], values[j], values[i].Type));
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
                      availableExpressions.Add(lowerThanExpr);
                    }
                    // Greater Equal = !(Lower than)
                    {
                      var geExpr = Expression.CreateNot(values[i].tok, Expression.CreateLess(values[i], values[j]));
                      availableExpressions.Add(geExpr);
                      negateOfExpressionIndex[availableExpressions.Count - 1] = availableExpressions.Count - 2;
                      negateOfExpressionIndex[availableExpressions.Count - 2] = availableExpressions.Count - 1;
                    }
                    // Lower Equal
                    {
                      var leExpr = Expression.CreateAtMost(values[i], values[j]);
                      availableExpressions.Add(leExpr);
                    }
                    // Greater Than = !(Lower equal)
                    {
                      var gtExpr = Expression.CreateNot(values[i].tok, Expression.CreateAtMost(values[i], values[j]));
                      availableExpressions.Add(gtExpr);
                      negateOfExpressionIndex[availableExpressions.Count - 1] = availableExpressions.Count - 2;
                      negateOfExpressionIndex[availableExpressions.Count - 2] = availableExpressions.Count - 1;
                    }
                  }
                }
              }
            }
          }
        }
      }
      if (!foundDesiredFunction) {
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
      dafnyMainExecutor.startAndWaitUntilAllProcessesFinishAndDumpTheirOutputs(true);

      for (int i = 0; i < availableExpressions.Count; i++) {
        UpdateCombinationResult(i);
      }

      for (int i = 0; i < bitArrayList.Count; i++) {
        // var ba = bitArrayList[i];
        // Console.WriteLine("------------------------------");
        Console.WriteLine(i + " : " +
                          Printer.ExprToString(availableExpressions[i]) + " : " +
                          combinationResults[i].ToString());
        // Console.WriteLine(ToBitString(ba, false));
        // Console.WriteLine("------------------------------");
      }

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
        dafnyMainExecutor.startAndWaitUntilAllProcessesFinishAndDumpTheirOutputs(true);
        for (int i = tmp; i < availableExpressions.Count; i++) {
          UpdateCombinationResult(i);
        }
        prevDepthExprStartIndex = tmp;
      }
      Console.WriteLine($"{dafnyMainExecutor.sw.ElapsedMilliseconds / 1000}:: finish exploring, try to calculate implies graph");
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
      if (combinationResults[0] == Result.CorrectProof) {
        Console.WriteLine("proof already goes through and no additional conjunction is needed!");
        return true;
      }
      List<int> correctExpressionsIndex = new List<int>();
      for (int i = 0; i < availableExpressions.Count; i++) {
        if (combinationResults[i] == Result.CorrectProof)
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
      dafnyImpliesExecutor.startAndWaitUntilAllProcessesFinishAndDumpTheirOutputs(false);
      Console.WriteLine($"{dafnyMainExecutor.sw.ElapsedMilliseconds / 1000}:: finish calculating implies, printing the dot graph");
      string graphVizOutput = $"digraph {funcName}_implies_graph {{\n";
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
        if (output.EndsWith("0 errors")) {
          Console.WriteLine($"edge from {availableExprAIndex} to {availableExprBIndex}");
          graphVizOutput += $"  {availableExprAIndex} -> {availableExprBIndex};\n";
        }
      }
      graphVizOutput += "}\n";
      File.WriteAllTextAsync($"/tmp/graph_{funcName}_implies.dot", graphVizOutput);
      Console.WriteLine($"{dafnyMainExecutor.sw.ElapsedMilliseconds / 1000}:: end");
      return true;
    }

    public void PrintImplies(Program program, Function func, int availableExprAIndex, int availableExprBIndex) {
      Console.WriteLine($"print implies {availableExprAIndex} {availableExprBIndex}");
      var funcName = func.FullDafnyName;
      string parameterNameTypes = "";
      foreach (var param in func.Formals) {
        parameterNameTypes += param.Name + ":" + param.Type.ToString() + ", ";
      }
      parameterNameTypes = parameterNameTypes.Remove(parameterNameTypes.Length - 2, 2);
      string lemmaForCheckingImpliesString = "lemma checkIfExprAImpliesExprB(";
      lemmaForCheckingImpliesString += parameterNameTypes + ")\n";
      Expression A = availableExpressions[availableExprAIndex];
      Expression B = availableExpressions[availableExprBIndex];
      lemmaForCheckingImpliesString += "  requires " + Printer.ExprToString(A) + "\n";
      lemmaForCheckingImpliesString += "  ensures " + Printer.ExprToString(B) + "\n";
      lemmaForCheckingImpliesString += "{}";

      int lemmaForCheckingImpliesPosition = 0;

      using (var wr = new System.IO.StringWriter()) {
        var pr = new Printer(wr);
        pr.UniqueStringBeforeUnderscore = UnderscoreStr;
        pr.PrintProgram(program, true);
        var code = $"// Implies {Printer.ExprToString(A)} ==> {Printer.ExprToString(B)}\n" + Printer.ToStringWithoutNewline(wr) + "\n\n";
        lemmaForCheckingImpliesPosition = code.Count(f => f == '\n') + 1;
        code += lemmaForCheckingImpliesString + "\n";
        File.WriteAllTextAsync($"/tmp/{funcName}_implies_{availableExprAIndex}_{availableExprBIndex}.dfy", code);
      }

      string dafnyBinaryPath = System.Reflection.Assembly.GetEntryAssembly().Location;
      dafnyBinaryPath = dafnyBinaryPath.Substring(0, dafnyBinaryPath.Length - 4);
      string env = CommandLineOptions.Clo.Environment.Remove(0, 22);
      var argList = env.Split(' ');
      string args = "";
      foreach (var arg in argList) {
        if (!arg.EndsWith(".dfy") && !arg.StartsWith("/holeEval") && !arg.StartsWith("/proc:")) {
          args += arg + " ";
        }
      }
      dafnyImpliesExecutor.createProcessWithOutput(dafnyBinaryPath,
        $"{args} /tmp/{funcName}_implies_{availableExprAIndex}_{availableExprBIndex}.dfy /proc:Impl*checkIfExprAImpliesExprB*",
        availableExprAIndex, availableExprBIndex, lemmaForCheckingImpliesPosition,
        $"{funcName}_implies_{availableExprAIndex}_{availableExprBIndex}.dfy");
    }

    public void PrintExprAndCreateProcess(Program program, Function func, Expression expr, int cnt) {
      Console.WriteLine($"{cnt} {Printer.ExprToString(expr)}");

      var funcName = func.FullDafnyName;
      string parameterNameTypes = "";
      string paramNames = "";
      foreach (var param in func.Formals) {
        parameterNameTypes += param.Name + ":" + param.Type.ToString() + ", ";
        paramNames += param.Name + ", ";
      }
      parameterNameTypes = parameterNameTypes.Remove(parameterNameTypes.Length - 2, 2);
      paramNames = paramNames.Remove(paramNames.Length - 2, 2);
      string lemmaForExprValidityString = "lemma checkReachableStatesNotBeFalse(";
      lemmaForExprValidityString += parameterNameTypes + ")\n";
      lemmaForExprValidityString += "  requires ";
      lemmaForExprValidityString += funcName + "(" + paramNames + ")\n";
      lemmaForExprValidityString += "  ensures false\n{}";
      int lemmaForExprValidityPosition = 0;

      using (var wr = new System.IO.StringWriter()) {
        var pr = new Printer(wr);
        pr.UniqueStringBeforeUnderscore = UnderscoreStr;
        func.Body = Expression.CreateAnd(func.Body, expr);
        pr.PrintProgram(program, true);
        var code = $"// {Printer.ExprToString(expr)}\n" + Printer.ToStringWithoutNewline(wr) + "\n\n";
        lemmaForExprValidityPosition = code.Count(f => f == '\n') + 1;
        code += lemmaForExprValidityString + "\n";
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
        if (!arg.EndsWith(".dfy") && !arg.StartsWith("/holeEval:")) {
          args += arg + " ";
        }
      }
      dafnyMainExecutor.createProcessWithOutput(dafnyBinaryPath,
          $"{args} /tmp/{funcName}_{cnt}.dfy /proc:*checkReachableStatesNotBeFalse*",
          expr, cnt, lemmaForExprValidityPosition, $"{funcName}_{cnt}");
      // Printer.PrintFunction(transformedFunction, 0, false);
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
      } else if (cl is TypeParameter) {
        var tp = (TypeParameter)cl;
        // Console.WriteLine($"{variable.Name} is TypeParameter");
        // TODO traverse underlying definition as well.
      } else if (cl is InternalTypeSynonymDecl) {
        var isyn = (InternalTypeSynonymDecl)cl;
        // Console.WriteLine($"{variable.Name} is InternalTypeSynonymDecl");
        // TODO traverse underlying definition as well.
      } else if (cl is NewtypeDecl) {
        var td = (NewtypeDecl)cl;
        Console.WriteLine($"{Printer.ExprToString(td.Constraint)} {td.Var.Name}");
        // TODO possibly figure out other expressions from td.Constraint
        if (td.BaseType is IntType) {
          var zeroLiteralExpr = Expression.CreateIntLiteral(expr.tok, 0);
          zeroLiteralExpr.Type = t;
          // Add the literal for maximum value of this newtype decl.
          yield return zeroLiteralExpr;
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
        }
        // Console.WriteLine($"{variable.Name} is SubsetTypeDecl");
        // TODO traverse underlying definition as well.
      } else if (cl is ClassDecl) {
        // Console.WriteLine($"{variable.Name} is ClassDecl");
        // TODO traverse underlying definition as well.
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