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
  public class ExpressionFinder {

    private int prevDepthExprStartIndex = 1;
    private int numberOfSingleExpr = 0;
    private MutationEvaluator mutationEval = null;
    private ProofEvaluator proofEval = null;

    private SpecInputOutputChecker specInputOutputChecker = null;
    public List<ExpressionDepth> availableExpressions = new List<ExpressionDepth>();
    private List<BitArray> bitArrayList = new List<BitArray>();
    private HashSet<string> currCombinations = new HashSet<string>();
    private Dictionary<string, int> bitArrayStringToIndex = new Dictionary<string, int>();
    public Dictionary<int, Result> combinationResults = new Dictionary<int, Result>();
    private Dictionary<int, int> negateOfExpressionIndex = new Dictionary<int, int>();

    public class ExpressionDepth  : IComparable<ExpressionDepth>, IEquatable<ExpressionDepth>{
      public Expression expr;
      public int depth;
      public ExpressionDepth(Expression expr, int depth) 
      {
        this.expr = expr;
        this.depth = depth;
      }
    public int Compare(ExpressionDepth a, ExpressionDepth b)
    {
        // Equal.
        if (a.expr == b.expr && a.depth == b.depth)
        {
            return 0;
        }
        // Less than.
        else
       return -1;
    }

   public int CompareTo(ExpressionDepth ed)
    {
        return Compare(this, ed);
    }

        public bool Equals(ExpressionDepth x)
      {
        //Check whether the compared objects reference the same data.
        if (Object.ReferenceEquals(this, x)) return true;

        //Check whether any of the compared objects is null.
        if (Object.ReferenceEquals(x, null))
            return false;
        
        int hashExpressionExpr = Printer.ExprToString(expr).GetHashCode();
        int xhashExpressionExpr = Printer.ExprToString(x.expr).GetHashCode();
        return hashExpressionExpr == xhashExpressionExpr;
        //  return Printer.ExprToString(expr).GetHashCode() == Printer.ExprToString(expr).GetHashCode();
        // return Printer.ExprToString(x.expr) == Printer.ExprToString(expr) && x.depth == depth;
      }

    }

    public class ExpressionDepthComparer : IEqualityComparer<ExpressionDepth>
    {
      public bool Equals(ExpressionDepth x, ExpressionDepth y)
      {
        //Check whether the compared objects reference the same data.
        if (Object.ReferenceEquals(x, y)) return true;

        //Check whether any of the compared objects is null.
        if (Object.ReferenceEquals(x, null) || Object.ReferenceEquals(y, null))
            return false;
        
        return x.expr.ToString() == y.expr.ToString() && x.depth == y.depth;
      }
      public int GetHashCode(ExpressionDepth e)
      {
        //Check whether the object is null
        if (Object.ReferenceEquals(e, null)) return 0;

        //Get hash code for the Name field if it is not null.
        int hashExpressionDepth = e.depth == null ? 0 : e.depth.GetHashCode();

        //Get hash code for the Code field.
        int hashExpressionExpr = e.expr.ToString().GetHashCode();

        //Calculate the hash code for the product.
        return hashExpressionExpr;// ^ hashExpressionDepth;
      }

    }

    public class StatementDepth {
      public Statement stmt;
      public int depth;
      public StatementDepth(Statement stmt, int depth) 
      {
        this.stmt = stmt;
        this.depth = depth;
      }
    }

    public ExpressionFinder(MutationEvaluator mutationEval) {
      this.mutationEval = mutationEval;
    }
    public ExpressionFinder(ProofEvaluator proofEval) {
      this.proofEval = proofEval;
    }

    public ExpressionFinder(SpecInputOutputChecker specInputOutputChecker){
      this.specInputOutputChecker = specInputOutputChecker;
    }

    private string ToBitString(BitArray bits, bool skipZero) {
      var sb = new StringBuilder();

      for (int i = skipZero ? 1 : 0; i < bits.Count; i++) {
        char c = bits[i] ? '1' : '0';
        sb.Append(c);
      }

      return sb.ToString();
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
      if ((!MutationEvaluator.IsGoodResult(combinationResults[indexI])) ||
          (!MutationEvaluator.IsGoodResult(combinationResults[indexJ]))) {
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
          if (!MutationEvaluator.IsGoodResult(combinationResults[index]))
            return false;
        }
        Increment(ref countBitArray);
      }
      return true;
    }

    public IEnumerable<ExpressionDepth> ExtendFunctionInvocationExpressions(Program program, IEnumerable<ExpressionDepth> expressionList) {
      foreach (var exprDepth in expressionList) {
        yield return exprDepth;
      }
      var typeToExpressionDict = GetTypeToExpressionDict(expressionList);
      foreach (var kvp in program.ModuleSigs) {
        foreach (var d in kvp.Value.ModuleDef.TopLevelDecls) {
          var cl = d as TopLevelDeclWithMembers;
          if (cl != null) {
            foreach (var member in cl.Members) {
              if (member is Function) {
                var functionInvocations = GetAllPossibleFunctionInvocations(program, member as Function, typeToExpressionDict);
                foreach (var invocation in functionInvocations) {
                  yield return invocation;
                }
              } else if (member is Predicate) {
                var predicateInvocations = GetAllPossiblePredicateInvocations(program, member as Predicate, typeToExpressionDict);
                foreach (var invocation in predicateInvocations) {
                  yield return invocation;
                }
              }
            }
          }
        }
      }
    }

    public IEnumerable<ExpressionDepth> ExtendInSeqExpressions(IEnumerable<ExpressionDepth> expressionList) {
      int maxEvalDepth = DafnyOptions.O.HoleEvaluatorExpressionDepth;
      foreach (var exprDepth in expressionList) {
        yield return exprDepth;
      }
      var typeToExpressionDict = GetTypeToExpressionDict(expressionList);
      foreach (var typeExprListTuple in typeToExpressionDict) {
        var typeStr = typeExprListTuple.Key;
        var exprHashSet = typeExprListTuple.Value;
        var exprHashSetAny = exprHashSet.Where(x => true).FirstOrDefault();
        if (exprHashSetAny.expr.Type.AsCollectionType != null) {
          var collectionElementType = exprHashSetAny.expr.Type.AsCollectionType.Arg;
          collectionElementType = LemmaFinder.SubstituteTypeWithSynonyms(collectionElementType);
          if (typeToExpressionDict.ContainsKey(collectionElementType.ToString())) {
            foreach (var elem in typeToExpressionDict[collectionElementType.ToString()]) {
              if (elem.depth + 1 > maxEvalDepth) {
                continue;
              }
              foreach (var collection in exprHashSet) {
                if (collection.depth + 1 > maxEvalDepth) {
                   continue;
                }
                if (!(collection.expr is FunctionCallExpr)) {
                  var InExpr = new BinaryExpr(elem.expr.tok, BinaryExpr.Opcode.In, elem.expr, collection.expr);
                    InExpr.Type = Type.Bool;
                  yield return new ExpressionDepth(InExpr, Math.Max(collection.depth, elem.depth) + 1);
                }
              }
            }
          }
        }
      }
    }

    public IEnumerable<ExpressionDepth> ExtendSeqSelectExpressions(IEnumerable<ExpressionDepth> expressionList) {
      // Console.WriteLine("here");
      int maxEvalDepth = DafnyOptions.O.HoleEvaluatorExpressionDepth;
      foreach (var exprDepth in expressionList) {
        yield return exprDepth;
      }
      var typeToExpressionDict = GetTypeToExpressionDict(expressionList);
      if (typeToExpressionDict.ContainsKey("int")) {
        var intVarHashSet = typeToExpressionDict["int"];
        foreach (var type in typeToExpressionDict.Keys) {
          var firstElem = typeToExpressionDict[type].Where(x => true).FirstOrDefault();
          if (firstElem.expr.Type is SeqType) {
            var seqVarHashSet = typeToExpressionDict[type];
            foreach (var seqVar in seqVarHashSet) {
              if (seqVar.depth + 1 > maxEvalDepth) {
                continue;
              }
            // for (int i = 0; i < seqVarList.Count; i++) {
              // var seqVar = seqVarList[i];
              foreach (var intVar in intVarHashSet) {
                if (intVar.depth + 1 > maxEvalDepth) {
                  continue;
                }
              // for (int j = 0; j < intVarList.Count; j++) {
                var seqSelectExpr = new SeqSelectExpr(seqVar.expr.tok, true, seqVar.expr, intVar.expr, null,null);
                seqSelectExpr.Type = (seqVar.expr.Type as SeqType).Arg;
                yield return new ExpressionDepth(seqSelectExpr, Math.Max(seqVar.depth, intVar.depth) + 1);
              }
            }
          }
        }
      }
      yield break;
    }

    public void CalcDepthOneAvailableExpresssionsFromFunctionBody(Program program, Function desiredFunction) {
      Contract.Requires(desiredFunction != null);
      Contract.Requires(availableExpressions.Count == 0);
      var expressions = ListArguments(program, desiredFunction);
      mutatePredidate(program, desiredFunction, expressions);
    }
    
    public void CalcDepthOneAvailableExpresssionsFromFunction(Program program, Function desiredFunction) {
      Contract.Requires(desiredFunction != null);
      Contract.Requires(availableExpressions.Count == 0);
      var expressions = ListArguments(program, desiredFunction);
      CalcDepthOneAvailableExpresssions(program, desiredFunction, expressions);
    }

    public void CalcDepthOneAvailableExpresssionsFromLemma(Program program, Lemma desiredLemma) {
      Contract.Requires(desiredLemma != null);
      Contract.Requires(availableExpressions.Count == 0);
      var expressions = ListArguments(program, desiredLemma);
      var extendedExpressions = ExtendSeqSelectExpressions(expressions);
      CalcDepthOneAvailableExpresssions(program, desiredLemma, extendedExpressions);
    }

     public Dictionary<string, HashSet<ExpressionDepth>> GetTypeToExpressionDict(IEnumerable<ExpressionDepth> expressionList) {
      int maxEvalDepth = DafnyOptions.O.HoleEvaluatorExpressionDepth;
      Dictionary<string, HashSet<ExpressionDepth>> typeToExpressionDict = new Dictionary<string, HashSet<ExpressionDepth>>();
      foreach (var exprDepth in expressionList) {
        var expr = exprDepth.expr;
        var exprString = Printer.ExprToString(expr);
        var typeString = expr.Type.ToString();
        // Console.WriteLine($"{c,2} {exprString,-20} {typeString}");
        if (expr.Type == Type.Bool && exprString[exprString.Length - 1] == '?') {
          typeString = "_questionMark_";
        }
        if (typeToExpressionDict.ContainsKey(typeString)) {
          // bool containsItem = typeToExpressionDict[typeString].Any(
          //      item => Printer.ExprToString(item.expr) == Printer.ExprToString(expr));
          // if (!containsItem) {
          typeToExpressionDict[typeString].Add(exprDepth);
          // }
        } else {
          var lst = new HashSet<ExpressionDepth>();
          lst.Add(exprDepth);
          typeToExpressionDict.Add(typeString, lst);
        }
        // AddExpression(program, topLevelDecl, expr);
      }
      return typeToExpressionDict;
    }

    public Dictionary<string, HashSet<ExpressionDepth>> GetRawExpressions(Program program, MemberDecl decl,
        IEnumerable<ExpressionDepth> expressions, bool addToAvailableExpressions) {
      var typeToExpressionDict = GetTypeToExpressionDict(expressions);
      // foreach (var kvp in program.ModuleSigs) {
      //   foreach (var d in kvp.Value.ModuleDef.TopLevelDecls) {
      //     var cl = d as TopLevelDeclWithMembers;
      //     if (cl != null) {
      //       foreach (var member in cl.Members) {
      //         if (member is Predicate) {
      //           var predicateInvocations = GetAllPossiblePredicateInvocations(program, member as Predicate, typeToExpressionDict);
      //           if (!typeToExpressionDict.ContainsKey("bool")) {
      //             typeToExpressionDict.Add("bool", new HashSet<ExpressionDepth>());
      //           }
      //           typeToExpressionDict["bool"].UnionWith(predicateInvocations);
      //         }
      //       }
      //     }
      //   }
      // }
      if (decl is Function) {
        var desiredFunction = decl as Function;
        var equalExprToCheck = desiredFunction.Body;
        foreach (var e in desiredFunction.Req) {
          equalExprToCheck = Expression.CreateAnd(equalExprToCheck, e.E);
        }
        Dictionary<string, List<string>> equalExprList = GetEqualExpressionList(equalExprToCheck);
        foreach (var k in equalExprList.Keys) {
          var t = equalExprList[k][0];
          if (typeToExpressionDict.ContainsKey(t)) {
            for (int i = 1; i < equalExprList[k].Count; i++) {
              foreach (var e in typeToExpressionDict[t]) {
              // for (int j = 0; j < typeToExpressionDict[t].Count; j++) {
                if (Printer.ExprToString(e.expr) == equalExprList[k][i]) {
                  typeToExpressionDict[t].Remove(e);
                  break;
                }
              }
            }
          }
        }
      }
      if (addToAvailableExpressions) {
        foreach (var t in typeToExpressionDict) {
          foreach (var e in t.Value) {
            availableExpressions.Add(e);
          }
        }
      }
      return typeToExpressionDict;
    }


    public void mutatePredidate(Program program, MemberDecl decl, IEnumerable<ExpressionDepth> expressions){
      foreach (ExpressionDepth e in mutatePredidateHelper(program,decl,expressions)){
        availableExpressions.Add(e);
      }
      // availableExpressions = mutatePredidateHelper(program,decl,expressions);
    }

    public bool IsNumericBasedExpression(Expression e)
    {
      
      return e != null 
            && e.Type != null 
            && (e.Type.IsNumericBased(Type.NumericPersuasion.Int) 
                || e.Type.IsNumericBased(Type.NumericPersuasion.Real) 
                || (e.Type.IsBigOrdinalType));
    }

    public bool isOpArith(BinaryExpr.Opcode op)
    {
      return (op == BinaryExpr.Opcode.Sub
            || op == BinaryExpr.Opcode.Add
            || op == BinaryExpr.Opcode.Mul
            || op == BinaryExpr.Opcode.Mod);
    }

    public static IEnumerable<ExpressionDepth> ListFunctionInvocations(
        Function func,
        Dictionary<string, HashSet<ExpressionDepth>> typeToExpressionDict,
        List<ExpressionDepth> arguments,
        int shouldFillIndex) {
      if (shouldFillIndex == func.Formals.Count) {
        List<ActualBinding> bindings = new List<ActualBinding>();
        var depth = 0;
        foreach (var arg in arguments) {
          bindings.Add(new ActualBinding(null, arg.expr));
          depth = Math.Max(depth, arg.depth);
        }
        var funcCallExpr = new FunctionCallExpr(func.tok, func.FullDafnyName, new ImplicitThisExpr(func.tok), func.tok,null, bindings);
        funcCallExpr.Type = func.ResultType;
        yield return new ExpressionDepth(funcCallExpr, depth);
        yield break;
      }
      var t = func.Formals[shouldFillIndex].Type;
      if (typeToExpressionDict.ContainsKey(t.ToString())) {
        foreach (var expr in typeToExpressionDict[t.ToString()]) {
          arguments.Add(expr);
          foreach (var ans in ListFunctionInvocations(func, typeToExpressionDict, arguments, shouldFillIndex + 1)) {
            yield return ans;
          }
          arguments.RemoveAt(arguments.Count - 1);
        }
      }
    }


public List<ExpressionDepth> mutateOneExpressionRevised(Program program, MemberDecl decl, ExpressionDepth e)
    {
      List<ExpressionDepth> currentExperssions = new List<ExpressionDepth>();
      if(e.expr == null || e.expr.Type == null)
      {
        return currentExperssions;
      }
    
      // }else{
      Console.WriteLine(" expression = " + e.expr + "( " + Printer.ExprToString(e.expr) + ") \n");
      //replacement mutations
      if(e.expr is NameSegment)
      {
        var f = decl as Function;
        if(f == null)
        {
          Method fm = decl as Method;
          var ens = e.expr as NameSegment;
          var ensTypeStr = Printer.GetFullTypeString(fm.EnclosingClass.EnclosingModuleDefinition, ens.Type, new HashSet<ModuleDefinition>(),true);

          foreach (var form in fm.Ins)
          {
            if(form.Name != ens.Name){
              var formTypeStr = Printer.GetFullTypeString(fm.EnclosingClass.EnclosingModuleDefinition, form.Type, new HashSet<ModuleDefinition>(),true);
              if(ensTypeStr == formTypeStr){
                var ns = new NameSegment(form.Tok, form.Name, null);
                currentExperssions.Add(new ExpressionDepth(ns,1));
              }
            }
          }

        }else{
          var ens = e.expr as NameSegment;
          var ensTypeStr = Printer.GetFullTypeString(f.EnclosingClass.EnclosingModuleDefinition, ens.Type, new HashSet<ModuleDefinition>(),true);

          foreach (var form in f.Formals)
          {
            if(form.Name != ens.Name){
              var formTypeStr = Printer.GetFullTypeString(f.EnclosingClass.EnclosingModuleDefinition, form.Type, new HashSet<ModuleDefinition>(),true);
              if(ensTypeStr == formTypeStr){
                var ns = new NameSegment(form.Tok, form.Name, null);
                currentExperssions.Add(new ExpressionDepth(ns,1));
              }
            }
          }
        }
      }
      if(e.expr is SeqSelectExpr)
      {
        var sse = e.expr as SeqSelectExpr;
        List<ExpressionDepth> sse_seq_mutations = mutateOneExpressionRevised(program, decl, new ExpressionDepth(sse.Seq != null ? sse.Seq : null,1));
        List<ExpressionDepth> sse_e0_mutations = mutateOneExpressionRevised(program, decl, new ExpressionDepth(sse.E0 != null ? sse.E0 : null,1));
        List<ExpressionDepth> sse_e1_mutations = mutateOneExpressionRevised(program, decl, new ExpressionDepth(sse.E1 != null ? sse.E1 : null,1));
        foreach (var seqM in sse_seq_mutations)
        {
          var sseMutatedSeq = new SeqSelectExpr(sse.tok,sse.SelectOne,seqM.expr,sse.E0,sse.E1,sse.CloseParen);
          currentExperssions.Add(new ExpressionDepth(sseMutatedSeq,1));
        }
        foreach (var e0M in sse_e0_mutations)
        {
          var sseMutatedE0 = new SeqSelectExpr(sse.tok,sse.SelectOne,sse.Seq,e0M.expr,sse.E1,sse.CloseParen);
          currentExperssions.Add(new ExpressionDepth(sseMutatedE0,1));
        }
        foreach (var e1M in sse_e1_mutations)
        {
          var sseMutatedE1 = new SeqSelectExpr(sse.tok,sse.SelectOne,sse.Seq,sse.E0,e1M.expr,sse.CloseParen);
          currentExperssions.Add(new ExpressionDepth(sseMutatedE1,1));
        }
      }
      if (e.expr is IdentifierExpr)
      {
        var ie = e.expr as IdentifierExpr;
       var t = new IdentifierExpr(ie.tok, "ie"+ie.Name);


      }
      if(e.expr is NestedMatchExpr)
      {
        var nme = e.expr as NestedMatchExpr;
        var me = nme.Resolved as MatchExpr;
        for (int i = 0; i < me.Cases.Count; i++){
          var subCase = me.Cases[i];
          List<ExpressionDepth> CaseMutations = mutateOneExpressionRevised(program, decl, new ExpressionDepth(subCase.Body,1));
          //    public NestedMatchExpr(IToken tok, Expression source, [Captured] List<NestedMatchCaseExpr> cases, bool usesOptionalBraces, Attributes attrs = null) : base(tok) {
          List<NestedMatchCaseExpr> mutatedCases = new List<NestedMatchCaseExpr>();
          for(int j = 0;j < me.Cases.Count; j++){
            if(!(j == i) && j<nme.Cases.Count)
            {
              mutatedCases.Add(nme.Cases[j]);
            }
          }
          foreach(var caseMutant in CaseMutations)
          {
            List<NestedMatchCaseExpr> mutatedSubCases = new List<NestedMatchCaseExpr>(mutatedCases);
            NestedMatchCaseExpr nmcExpr = new NestedMatchCaseExpr(nme.Cases[i].Tok,nme.Cases[i].Pat,caseMutant.expr,nme.Cases[i].Attributes);
            mutatedSubCases.Add(nmcExpr);
            NestedMatchExpr nmeMutated = new NestedMatchExpr(nme.tok,nme.Source,mutatedSubCases,nme.UsesOptionalBraces,nme.Attributes);
            currentExperssions.Add(new ExpressionDepth(nmeMutated,1));
          }
        }

      }
      if(e.expr is NestedMatchCaseExpr)
      {
        // var nmce = e.expr as NestedMatchCaseExpr;
      }
      if(e.expr is ExprDotName)
      {
        var expDotN = e.expr as ExprDotName;
        List<ExpressionDepth> NameMutationsLhs = mutateOneExpressionRevised(program, decl, new ExpressionDepth(expDotN.Lhs,1));
        foreach (var nml in NameMutationsLhs)
        {
          var edn = new ExprDotName(expDotN.tok,nml.expr,expDotN.SuffixName,expDotN.OptTypeArguments);
          currentExperssions.Add(new ExpressionDepth(edn,1));
        } 
      }


      if(e.expr is ITEExpr)
      {
        var itee = e.expr as ITEExpr;
        List<ExpressionDepth> Test = mutateOneExpressionRevised(program, decl, new ExpressionDepth(itee.Test,1));
        List<ExpressionDepth> Thn = mutateOneExpressionRevised(program, decl, new ExpressionDepth(itee.Thn,1));
        List<ExpressionDepth> Else = mutateOneExpressionRevised(program, decl, new ExpressionDepth(itee.Els,1));
        foreach (var t in Test)
        {
          var iteT = new ITEExpr(e.expr.tok,itee.IsBindingGuard,t.expr,itee.Thn,itee.Els);
          currentExperssions.Add(new ExpressionDepth(iteT,1));
        }
        foreach (var th in Thn)
        {
          var iteThn = new ITEExpr(e.expr.tok,itee.IsBindingGuard,itee.Test,th.expr,itee.Els);
          currentExperssions.Add(new ExpressionDepth(iteThn,1));
        }
        foreach (var el in Else)
        {
          var iteEls = new ITEExpr(e.expr.tok,itee.IsBindingGuard,itee.Test,itee.Thn,el.expr);
          currentExperssions.Add(new ExpressionDepth(iteEls,1));
        }

      }
      if(e.expr is ApplySuffix)
      {
      //negation of ApplySuffix
      currentExperssions.Add(new ExpressionDepth(Expression.CreateNot(e.expr.tok,e.expr),1));
      }
      if(e.expr is OldExpr)
      {
              // currentExperssions.Add(new ExpressionDepth(Expression.CreateNot(e.expr.tok,e.expr),1));
          currentExperssions.Add(new ExpressionDepth((e.expr as OldExpr).E,1));

      }
      if(e.expr is LiteralExpr)
      {
        currentExperssions.Add(e);
              if ((e.expr.Type.IsNumericBased(Type.NumericPersuasion.Int) 
              || e.expr.Type.IsNumericBased(Type.NumericPersuasion.Real)))
        {
          var lit = e.expr as LiteralExpr;

          var inc = Expression.CreateIncrement(e.expr, 1);
          var dec = Expression.CreateDecrement(e.expr, 1);
          currentExperssions.Add(new ExpressionDepth(inc,1));
          currentExperssions.Add(new ExpressionDepth(dec,1));
        }
      }
      if(e.expr is LetExpr)
      {
        var le = e.expr as LetExpr;
        Console.WriteLine( Printer.ExprToString(le.Body));
        List<ExpressionDepth> Rhs = mutateOneExpressionRevised(program, decl, new ExpressionDepth(le.RHSs[0],1));
        List<ExpressionDepth> bdy = mutateOneExpressionRevised(program, decl, new ExpressionDepth(le.Body,1));
        // foreach (var rs in Rhs)
        // {
        //   List<Expression> r = new List<Expression>();
        //   r.Add(rs.expr);
        //   foreach (var b in bdy)
        //   {
        //     var nleExpr = new LetExpr(e.expr.tok,le.LHSs,r,b.expr,true);
        //     currentExperssions.Add(new ExpressionDepth(nleExpr,1));
        //   }
        // }
        // Console.WriteLine( Printer.ExprToString(le.Body));
                // foreach (var rs in Rhs)
        foreach (var rs in Rhs)
        {
          List<Expression> r = new List<Expression>();
          r.Add(rs.expr);
          // foreach (var b in bdy)
          // {
            var RhsLeExpr = new LetExpr(e.expr.tok,le.LHSs,r,le.Body,true);
            currentExperssions.Add(new ExpressionDepth(RhsLeExpr,1));
          // }
        }
        foreach(var b in bdy)
        {
          var nleExpr = new LetExpr(e.expr.tok,le.LHSs,le.RHSs,b.expr,true);
          currentExperssions.Add(new ExpressionDepth(nleExpr,1));
        }
      }
      if (e.expr is ParensExpression)
      {
        var pE = e.expr as ParensExpression;
        // e.expr = pE.E as BinaryExpr;
        List<ExpressionDepth> parensE = mutateOneExpressionRevised(program, decl, new ExpressionDepth(pE.E,1));
        foreach (var pee in parensE)
        {
          ParensExpression pEMutated = new ParensExpression(e.expr.tok,pee.expr);
          currentExperssions.Add(new ExpressionDepth(pEMutated,1));
        }
        
      }
      if(e.expr is BinaryExpr)
      {
        var be = e.expr as BinaryExpr;
        //logical
        if(be.Op == BinaryExpr.Opcode.Iff
           || be.Op == BinaryExpr.Opcode.Imp
           || be.Op == BinaryExpr.Opcode.And
           || be.Op == BinaryExpr.Opcode.Or)
        {
          // Console.WriteLine("logical");
          //LOR (Logical Operator Replacement)
          // OR = (a || b)
          var Or = Expression.CreateOr(be.E0, be.E1,false);
          // Not A OR = (!a || b)
          var OrNotA = Expression.CreateOr(Expression.CreateNot(be.tok, be.E0), be.E1,false);
          // Not B OR = (a || !b)
          var OrNotB = Expression.CreateOr(be.E0,Expression.CreateNot(be.tok, be.E1),false);
           // Not A Not B OR = (!a || !b)
          var OrNotANotB = Expression.CreateOr(Expression.CreateNot(be.tok, be.E0),Expression.CreateNot(be.tok, be.E1),false);
          // AND = (a && b)
          var And = Expression.CreateAnd(be.E0, be.E1,false);
          // Not A AND = (!a && b)
          var AndNotA = Expression.CreateAnd(Expression.CreateNot(be.tok, be.E0), be.E1,false);
          // Not B AND = (a && !b)
          var AndNotB = Expression.CreateAnd(be.E0,Expression.CreateNot(be.tok, be.E1),false);
          // Not A Not B AND = (!a && !b)
          var AndNotANotB = Expression.CreateAnd(Expression.CreateNot(be.tok, be.E0),Expression.CreateNot(be.tok, be.E1),false);
         
          currentExperssions.Add(new ExpressionDepth(Or,1));
          currentExperssions.Add(new ExpressionDepth(OrNotA,1));
          currentExperssions.Add(new ExpressionDepth(OrNotB,1));
          currentExperssions.Add(new ExpressionDepth(OrNotANotB,1));

          currentExperssions.Add(new ExpressionDepth(And,1));
          currentExperssions.Add(new ExpressionDepth(AndNotA,1));
          currentExperssions.Add(new ExpressionDepth(AndNotB,1));
          currentExperssions.Add(new ExpressionDepth(AndNotANotB,1));
        }
        //Relational
        if(be.Op == BinaryExpr.Opcode.Lt
           || be.Op == BinaryExpr.Opcode.Le
           || be.Op == BinaryExpr.Opcode.Ge
           || be.Op == BinaryExpr.Opcode.Gt
           || be.Op == BinaryExpr.Opcode.Eq)
        {
          // Console.WriteLine("Relational Expr");
          //RORB (Binary Relational Replacemnt)
          // Lower than
          var LessT = Expression.CreateLess(be.E0, be.E1);
          // Lower Equal
          var AtMost = Expression.CreateAtMost(be.E0, be.E1);
          // Greater Than = !(Lower equal)
          var gtExpr = Expression.CreateNot(be.tok, Expression.CreateAtMost(be.E0, be.E1));
          // Greater Equal = !(Lower than)
          var geExpr = Expression.CreateNot(be.tok, Expression.CreateLess(be.E0, be.E1));
          //Equal
          var equalityExpr = Expression.CreateEq(be.E0, be.E1,be.Type);
           // Not Equal = !(a == b)
          var NotEquals = Expression.CreateNot(be.tok, Expression.CreateEq(be.E0, be.E1,be.Type));

          currentExperssions.Add(new ExpressionDepth(LessT,1)); 
          currentExperssions.Add(new ExpressionDepth(AtMost,1)); 
          currentExperssions.Add(new ExpressionDepth(gtExpr,1)); 
          currentExperssions.Add(new ExpressionDepth(geExpr,1));
          currentExperssions.Add(new ExpressionDepth(equalityExpr,1));
          currentExperssions.Add(new ExpressionDepth(NotEquals,1));

        }
        //Arith
      if(be.Op == BinaryExpr.Opcode.Add
           || be.Op == BinaryExpr.Opcode.Sub
           || be.Op == BinaryExpr.Opcode.Div
           || be.Op == BinaryExpr.Opcode.Mod)
        {
          // Console.WriteLine("Arith");
          //AORB (Binary Arithmatic Operator Replacement)
          //Add
          var AddExpr = Expression.CreateAdd(be.E0, be.E1);
          //Sub
          var SubExpr = Expression.CreateSubtract(be.E0, be.E1);
          //Mult
          var MultExpr = Expression.CreateMul(be.E0, be.E1);
          //Div
          var DivExpr = Expression.CreateDiv(be.E0, be.E1);
          //Mod
          var ModExpr = Expression.CreateMod(be.E0, be.E1);
          currentExperssions.Add(new ExpressionDepth(AddExpr,1));
          currentExperssions.Add(new ExpressionDepth(SubExpr,1));
          currentExperssions.Add(new ExpressionDepth(MultExpr,1));
          currentExperssions.Add(new ExpressionDepth(DivExpr,1));
          currentExperssions.Add(new ExpressionDepth(ModExpr,1));
        }
      if ((be.Type.IsNumericBased(Type.NumericPersuasion.Int) 
              || be.Type.IsNumericBased(Type.NumericPersuasion.Real))
              || (be).E0.Type.IsNumericBased(Type.NumericPersuasion.Int)
              || (be).E0.Type.IsNumericBased(Type.NumericPersuasion.Int)
              || (be).E1.Type.IsNumericBased(Type.NumericPersuasion.Real)
              || (be).E1.Type.IsNumericBased(Type.NumericPersuasion.Real))
        {
          //CRCR (Integer Constant Replacement)
          //AInc
          var Ainc = new BinaryExpr(be.tok, be.Op, Expression.CreateIncrement(be.E0, 1), be.E1);
          //BInc
          var Binc = new BinaryExpr(be.tok, be.Op,be.E0, Expression.CreateIncrement(be.E1, 1));
          //ADec
          var Adec = new BinaryExpr(be.tok, be.Op, Expression.CreateDecrement(be.E0, 1), be.E1);
          //BDec
          var Bdec = new BinaryExpr(be.tok, be.Op,be.E0, Expression.CreateDecrement(be.E1, 1));
          currentExperssions.Add(new ExpressionDepth(Ainc,1));
          currentExperssions.Add(new ExpressionDepth(Binc,1));
          currentExperssions.Add(new ExpressionDepth(Adec,1));
          currentExperssions.Add(new ExpressionDepth(Bdec,1));
        }

      //Set
      if(be.Op == BinaryExpr.Opcode.In)
        {
          // Console.WriteLine("SET Expr");
          // NotIn
          var NotIn = Expression.CreateNot(be.tok, be);
          currentExperssions.Add(new ExpressionDepth(NotIn,1));
        } 

        List<ExpressionDepth> subExperssionsE0 = mutateOneExpressionRevised(program,decl,new ExpressionDepth(be.E0,1));
        foreach (var subE0 in subExperssionsE0)
        {
          var sube0_new = new BinaryExpr(be.tok, be.Op, subE0.expr, be.E1);
          currentExperssions.Add(new ExpressionDepth(sube0_new,1));
        }

        List<ExpressionDepth> subExperssionsE1 = mutateOneExpressionRevised(program,decl,new ExpressionDepth(be.E1,1));
        foreach (var subE1 in subExperssionsE1)
        {
          var sube1_new = new BinaryExpr(be.tok, be.Op, be.E0, subE1.expr);
          currentExperssions.Add(new ExpressionDepth(sube1_new,1));
        }


      }else if(e.expr is ForallExpr)
      {
        // Console.WriteLine("Forall Expr");
         var eforall = e.expr as ForallExpr;
        //Mutate Term
        List<ExpressionDepth> forallExprs =  mutateOneExpressionRevised(program,decl,new ExpressionDepth(eforall.Term,1));
        foreach (ExpressionDepth ee in forallExprs){
          QuantifierExpr qe;
          ResolvedCloner cloner = new ResolvedCloner();
          var newVars = eforall.BoundVars.ConvertAll(cloner.CloneBoundVar);
          qe = new ForallExpr(eforall.tok, eforall.BodyEndTok, newVars, eforall.Range, ee.expr, eforall.Attributes);
          currentExperssions.Add(new ExpressionDepth(qe,1));
        }
        //Mutate Range
        List<ExpressionDepth> forallExprsRange =  mutateOneExpressionRevised(program,decl,new ExpressionDepth(eforall.Range,1));
        foreach (ExpressionDepth ee in forallExprsRange){
          QuantifierExpr qe;
          ResolvedCloner cloner = new ResolvedCloner();
          var newVars = eforall.BoundVars.ConvertAll(cloner.CloneBoundVar);
          qe = new ForallExpr(eforall.tok, eforall.BodyEndTok, newVars, ee.expr, eforall.Term, eforall.Attributes);
          currentExperssions.Add(new ExpressionDepth(qe,1));
        }
                   //negation of Forall
      currentExperssions.Add(new ExpressionDepth(Expression.CreateNot(eforall.tok,eforall),1));

      }else if(e.expr is ExistsExpr)
      {
        // Console.WriteLine("Exists Expr");
        var existsE = e.expr as ExistsExpr;
        // var be = e.LogicalBody() as BinaryExpr;
        List<ExpressionDepth> existsExprTerm = mutateOneExpressionRevised(program,decl,new ExpressionDepth(existsE.Term,1));
        List<ExpressionDepth> existsExpr = new List<ExpressionDepth>();

        foreach (ExpressionDepth ee in existsExprTerm){
          ExistsExpr q;
          ResolvedCloner cloner = new ResolvedCloner();
          var newVars = existsE.BoundVars.ConvertAll(cloner.CloneBoundVar);

          q = new ExistsExpr(existsE.tok, existsE.BodyEndTok, newVars, existsE.Range, ee.expr, existsE.Attributes);
          // ee = q;
          currentExperssions.Add(new ExpressionDepth(q,1));
        }
        // return existsExpr;

      }
      else if(e.expr is UnaryOpExpr)
      {
        // Console.WriteLine("Unary Expr");
      var ue = e.expr as UnaryOpExpr;
        if(ue.Op == UnaryOpExpr.Opcode.Not) // NOT
        {
            //DeleteNot
          currentExperssions.Add(new ExpressionDepth(ue.E,1));
          List<ExpressionDepth> subExperssionsE = mutateOneExpressionRevised(program,decl,new ExpressionDepth(ue.E,1));
          foreach (var subE in subExperssionsE)
          {
            // var sube_new = new BinaryExpr(be.tok, be.Op, subE.expr, ue.E);
            currentExperssions.Add(new ExpressionDepth(subE.expr,1));
          }
        }
        if(ue.Op == UnaryOpExpr.Opcode.Cardinality)
        {
          List<ExpressionDepth> subExperssionsE = mutateOneExpressionRevised(program,decl,new ExpressionDepth(ue.E,1));
          foreach (var subE in subExperssionsE)
          {
            // var sube_new = new BinaryExpr(be.tok, be.Op, subE.expr, ue.E);
            currentExperssions.Add(new ExpressionDepth(Expression.CreateCardinality(subE.expr,program.BuiltIns),1));
          }
        }
      }
        

      // Console.WriteLine("--REVISED-- "+ Printer.ExprToString(e.expr));
      // foreach (ExpressionDepth ed in currentExperssions)
      // {
      //   Console.WriteLine(Printer.ExprToString(ed.expr));
      // }
      // Console.WriteLine("---------");
      return currentExperssions;
    }
    public List<ExpressionDepth> mutateOneExpression(Program program, MemberDecl decl, ExpressionDepth e)
    {
      List<ExpressionDepth> currentExperssions = new List<ExpressionDepth>();
      // Console.WriteLine("Checking Exper" + Printer.ExprToString(e.expr));
      //       Console.WriteLine("Checking Type" + e.expr);
      // if(e.expr is ParensExpression)
      // {
      //   var rbe =  e.expr as BinaryExpr;
      // }
      List<ExpressionDepth> currentExperssions2 = mutateOneExpressionRevised(program,decl,e);
      if (e.expr is ParensExpression)
      {
        var pE = e.expr as ParensExpression;
        e.expr = pE.E as BinaryExpr;
      }
       if(e.expr is BinaryExpr || e.expr is ParensExpression)
       {
         if((e.expr as BinaryExpr).E0.Type is BoolType || (e.expr as BinaryExpr).E1.Type is BoolType){
          var be = e.expr as BinaryExpr;
          Console.WriteLine("MUTATING One Binary Expr= " + Printer.ExprToString(be));
                    // Console.WriteLine(" Binary OP = " + be.Op);

          var e0 = Printer.ExprToString(be.E0);
          var e1 = Printer.ExprToString(be.E1);
          // Console.WriteLine(be.E0);
          // Console.WriteLine(be.E1);
          // Console.WriteLine(be);
          var isNE0 = IsNumericBasedExpression(be.E0);
          var isNE1 = IsNumericBasedExpression(be.E1);
          var isArith = isOpArith(be.Op);
          //Equal
          var equalityExpr = Expression.CreateEq(be.E0, be.E1,be.Type);
          // OR = (a || b)
          var Or = Expression.CreateOr(be.E0, be.E1,false);
          // Not A OR = (!a || b)
          var OrNotA = Expression.CreateOr(Expression.CreateNot(be.tok, be.E0), be.E1,false);
          // Not B OR = (a || !b)
          var OrNotB = Expression.CreateOr(be.E0,Expression.CreateNot(be.tok, be.E1),false);
           // Not A Not B OR = (!a || !b)
          var OrNotANotB = Expression.CreateOr(Expression.CreateNot(be.tok, be.E0),Expression.CreateNot(be.tok, be.E1),false);
          // AND = (a && b)
          var And = Expression.CreateAnd(be.E0, be.E1,false);
          // Not A AND = (!a && b)
          var AndNotA = Expression.CreateAnd(Expression.CreateNot(be.tok, be.E0), be.E1,false);
          // Not B AND = (a && !b)
          var AndNotB = Expression.CreateAnd(be.E0,Expression.CreateNot(be.tok, be.E1),false);
          // Not A Not B AND = (!a && !b)
          var AndNotANotB = Expression.CreateAnd(Expression.CreateNot(be.tok, be.E0),Expression.CreateNot(be.tok, be.E1),false);
          // Not = !(E)
          var NotE = Expression.CreateNot(be.tok, be);
          // Not Equal = !(a == b)
          var NotEquals = Expression.CreateNot(be.tok, Expression.CreateEq(be.E0, be.E1,be.Type));
          // // Lower than
          // var LessT = Expression.CreateLess(be.E0, be.E1);
          // // Lower Equal
          // var AtMost = Expression.CreateAtMost(be.E0, be.E1);
          // // Greater Than = !(Lower equal)
          // var gtExpr = Expression.CreateNot(be.tok, Expression.CreateAtMost(be.E0, be.E1));
          // // Greater Equal = !(Lower than)
          // var geExpr = Expression.CreateNot(be.tok, Expression.CreateLess(be.E0, be.E1));
          // Implies
          var implies = Expression.CreateImplies(be.E0, be.E1);
          // Not A Implies = !a ==> b
          var impliesNotA = Expression.CreateImplies(Expression.CreateNot(be.tok, be.E0), be.E1);
          // Not B Implies = a ==> !b
          var impliesNotB = Expression.CreateImplies(be.E0,Expression.CreateNot(be.tok, be.E1));
          // Not A Not B Implies = !a ==> !b
          var impliesNotANotB = Expression.CreateImplies(Expression.CreateNot(be.tok, be.E0),Expression.CreateNot(be.tok, be.E1));
          // ImpliesReverse
          var impliesRev = Expression.CreateImplies(be.E1, be.E0);
          // Bi Implies
          var biConImplies = Expression.CreateAnd(Expression.CreateImplies(be.E0, be.E1), Expression.CreateImplies(be.E1, be.E0),false); 

          // new ExpressionDepth(e, 1)
          currentExperssions.Add(new ExpressionDepth(equalityExpr,1));
          currentExperssions.Add(new ExpressionDepth(Or,1));
          currentExperssions.Add(new ExpressionDepth(OrNotA,1));
          currentExperssions.Add(new ExpressionDepth(OrNotB,1));
          currentExperssions.Add(new ExpressionDepth(OrNotANotB,1));

          currentExperssions.Add(new ExpressionDepth(And,1));
          currentExperssions.Add(new ExpressionDepth(AndNotA,1));
          currentExperssions.Add(new ExpressionDepth(AndNotB,1));
          currentExperssions.Add(new ExpressionDepth(AndNotANotB,1));

          // currentExperssions.Add(new ExpressionDepth(NotE,1)); // Logically equivalent to OrNotANotB
          currentExperssions.Add(new ExpressionDepth(NotEquals,1));
          // currentExperssions.Add(new ExpressionDepth(LessT,1)); // Consider moving to Arith
          // currentExperssions.Add(new ExpressionDepth(AtMost,1)); // Consider moving to Arith
          // currentExperssions.Add(new ExpressionDepth(gtExpr,1)); // Consider moving to Arith
          // currentExperssions.Add(new ExpressionDepth(geExpr,1)); // Consider moving to Arith

          // currentExperssions.Add(new ExpressionDepth(implies,1)); // Logically equivalent to OrNotA
          // currentExperssions.Add(new ExpressionDepth(impliesNotA,1)); // Logically equivalent to OR
          // currentExperssions.Add(new ExpressionDepth(impliesNotB,1)); // Logically equivalent to OrNotANotB
          // currentExperssions.Add(new ExpressionDepth(impliesNotANotB,1)); // Logically equivalent to OrNotB
          // currentExperssions.Add(new ExpressionDepth(impliesRev,1));   // Logically equivalent to OrNotB
          // currentExperssions.Add(new ExpressionDepth(biConImplies,1));  // Logically equivalent to equalityExpr
          
          // if(be.E0 is BinaryExpr)
          // {
            List<ExpressionDepth> subExperssionsE0 = mutateOneExpression(program,decl,new ExpressionDepth(be.E0,1));
            foreach (var subE0 in subExperssionsE0)
            {
              var sube0_new = new BinaryExpr(be.tok, be.Op, subE0.expr, be.E1);
              currentExperssions.Add(new ExpressionDepth(sube0_new,1));
            }
            // currentExperssions.AddRange(mutateOneExpression(program,decl,new ExpressionDepth(be.E0,1)));
          // }
          // if(be.E1 is BinaryExpr)
          // {
            List<ExpressionDepth> subExperssionsE1 = mutateOneExpression(program,decl,new ExpressionDepth(be.E1,1));
            foreach (var subE1 in subExperssionsE1)
            {
              var sube1_new = new BinaryExpr(be.tok, be.Op, be.E0, subE1.expr);
              currentExperssions.Add(new ExpressionDepth(sube1_new,1));
            }
          // }
         }
       
       
          if ((e.expr.Type.IsNumericBased(Type.NumericPersuasion.Int) 
              || e.expr.Type.IsNumericBased(Type.NumericPersuasion.Real))
              || (e.expr as BinaryExpr).E0.Type.IsNumericBased(Type.NumericPersuasion.Int)
              || (e.expr as BinaryExpr).E0.Type.IsNumericBased(Type.NumericPersuasion.Int)
              || (e.expr as BinaryExpr).E1.Type.IsNumericBased(Type.NumericPersuasion.Real)
              || (e.expr as BinaryExpr).E1.Type.IsNumericBased(Type.NumericPersuasion.Real)) // what if it is a numeric data type? 
       {
          Console.WriteLine(Printer.ExprToString(e.expr) + " :: " + e.expr);
          var be = e.expr as BinaryExpr;
          Console.WriteLine("MUTATING Algebraic= " + Printer.ExprToString(be));
                    // Console.WriteLine(" Algebraic OP = " + be.Op);

         // var Ae = e.expr as ParensExpression;
          //Add
          var AddExpr = Expression.CreateAdd(be.E0, be.E1);
          //Sub
          var SubExpr = Expression.CreateSubtract(be.E0, be.E1);
          //Mult
          var MultExpr = Expression.CreateMul(be.E0, be.E1);
          //Div
          var DivExpr = Expression.CreateDiv(be.E0, be.E1);
          //Mod
          var ModExpr = Expression.CreateMod(be.E0, be.E1);
          //AInc
          var Ainc = new BinaryExpr(be.tok, be.Op, Expression.CreateIncrement(be.E0, 1), be.E1);
          //BInc
          var Binc = new BinaryExpr(be.tok, be.Op,be.E0, Expression.CreateIncrement(be.E1, 1));
          //ADec
          var Adec = new BinaryExpr(be.tok, be.Op, Expression.CreateDecrement(be.E0, 1), be.E1);
          //BDec
          var Bdec = new BinaryExpr(be.tok, be.Op,be.E0, Expression.CreateDecrement(be.E1, 1));

          // Lower than
          var LessT = Expression.CreateLess(be.E0, be.E1);
          // Lower Equal
          var AtMost = Expression.CreateAtMost(be.E0, be.E1);
          // Greater Than = !(Lower equal)
          var gtExpr = Expression.CreateNot(be.tok, Expression.CreateAtMost(be.E0, be.E1));
          // Greater Equal = !(Lower than)
          var geExpr = Expression.CreateNot(be.tok, Expression.CreateLess(be.E0, be.E1));



          currentExperssions.Add(new ExpressionDepth(AddExpr,1));
          currentExperssions.Add(new ExpressionDepth(SubExpr,1));
          currentExperssions.Add(new ExpressionDepth(MultExpr,1));
          currentExperssions.Add(new ExpressionDepth(DivExpr,1));
          currentExperssions.Add(new ExpressionDepth(ModExpr,1));
          currentExperssions.Add(new ExpressionDepth(Ainc,1));
          currentExperssions.Add(new ExpressionDepth(Binc,1));
          currentExperssions.Add(new ExpressionDepth(Adec,1));
          currentExperssions.Add(new ExpressionDepth(Bdec,1));
          currentExperssions.Add(new ExpressionDepth(LessT,1)); // Consider moving to Arith
          currentExperssions.Add(new ExpressionDepth(AtMost,1)); // Consider moving to Arith
          currentExperssions.Add(new ExpressionDepth(gtExpr,1)); // Consider moving to Arith
          currentExperssions.Add(new ExpressionDepth(geExpr,1)); // Consider moving to Arith

          List<ExpressionDepth> subExperssionsE0 = mutateOneExpression(program,decl,new ExpressionDepth(be.E0,1));
            foreach (var subE0 in subExperssionsE0)
            {
              var sube0_new = new BinaryExpr(be.tok, be.Op, subE0.expr, be.E1);
              currentExperssions.Add(new ExpressionDepth(sube0_new,1));
            }
            // currentExperssions.AddRange(mutateOneExpression(program,decl,new ExpressionDepth(be.E0,1)));
          // }
          // if(be.E1 is BinaryExpr)
          // {
            List<ExpressionDepth> subExperssionsE1 = mutateOneExpression(program,decl,new ExpressionDepth(be.E1,1));
            foreach (var subE1 in subExperssionsE1)
            {
              var sube1_new = new BinaryExpr(be.tok, be.Op, be.E0, subE1.expr);
              currentExperssions.Add(new ExpressionDepth(sube1_new,1));
            }


        } 
       }else if(e.expr is ForallExpr)
       {
        Console.WriteLine("nested forall ");
        var eforall = e.expr as ForallExpr;
        //Mutate Term
        List<ExpressionDepth> forallExprs =  mutateOneExpression(program,decl,new ExpressionDepth(eforall.Term as BinaryExpr,1));
        foreach (ExpressionDepth ee in forallExprs){
          QuantifierExpr qe;
          ResolvedCloner cloner = new ResolvedCloner();
          var newVars = eforall.BoundVars.ConvertAll(cloner.CloneBoundVar);
          qe = new ForallExpr(eforall.tok, eforall.BodyEndTok, newVars, eforall.Range, ee.expr, eforall.Attributes);
          currentExperssions.Add(new ExpressionDepth(qe,1));
        }
        //Mutate Range
        List<ExpressionDepth> forallExprsRange =  mutateOneExpression(program,decl,new ExpressionDepth(eforall.Range as BinaryExpr,1));
        foreach (ExpressionDepth ee in forallExprsRange){
          QuantifierExpr qe;
          ResolvedCloner cloner = new ResolvedCloner();
          var newVars = eforall.BoundVars.ConvertAll(cloner.CloneBoundVar);
          qe = new ForallExpr(eforall.tok, eforall.BodyEndTok, newVars, ee.expr, eforall.Term, eforall.Attributes);
          currentExperssions.Add(new ExpressionDepth(qe,1));
        }
           //negation of Forall
      currentExperssions.Add(new ExpressionDepth(Expression.CreateNot(eforall.tok,eforall),1));
       }

   
      return currentExperssions;
    }
// Mutate the body and params
    public List<ExpressionDepth> getMutatedExprs(Program program, Function decl, Expression expression){
      List<ExpressionDepth> currentExperssions = new List<ExpressionDepth>();
      List<List<ExpressionDepth>> combinations = new List<List<ExpressionDepth>>();
      List<List<String>> testS = new List<List<String>>();  
      Console.WriteLine("Full Expresion -> "+ Printer.ExprToString(expression));
      // Console.WriteLine("Expresion type = " + expression);
      var trueExpr = Expression.CreateBoolLiteral(decl.tok, true);
      var falseExpr = Expression.CreateBoolLiteral(decl.tok, false);
      IEnumerable<ExpressionDepth> q = TraverseFormal(program,new ExpressionDepth(expression,1));
      // currentExperssions.AddRange(mutateOneExpression(program,decl,q.ElementAt(0)));
      // List<ExpressionDepth> aaa =  mutateOneExpressionRevised(program,decl,new ExpressionDepth(expression,1));
      // currentExperssions.AddRange(mutateOneExpressionRevised(program,decl,new ExpressionDepth(expression,1)));

      // foreach (var e in currentExperssions)
      // {
      //   Console.WriteLine("initial= " + Printer.ExprToString(e.expr));

      // }
      // test
        currentExperssions = mutateOneExpressionRevised(program,decl,new ExpressionDepth(expression,1));
      //   Console.WriteLine("COUNT = "+currentExperssionsTEST.Count);
      //  foreach (var eli in currentExperssionsTEST){
      //   Console.WriteLine("TEST : = " + Printer.ExprToString(eli.expr));
      //  }
//end test

// 
/*
            List<Expression> conjuncts = Expression.Conjuncts(expression).ToList();
        if(conjuncts.Count == 1)
        {
          Console.WriteLine("Single Conjunct => "+ conjuncts.Count);
          // var be = expression as BinaryExpr;
          // Console.WriteLine("here = " + expression);
          // Console.WriteLine("HERE 2-> "+ Printer.ExprToString(be));
          // currentExperssions = mutateOneExpression(program,decl,new ExpressionDepth(be,1));
          currentExperssions = mutateOneExpressionRevised(program,decl,new ExpressionDepth(expression,1));

        }
        if(conjuncts.Count > 1){
        for (int i = 0; i < conjuncts.Count; i++) {
          Console.WriteLine("Whole EXPRESSION To Mutate= " + Printer.ExprToString(conjuncts[i]));
          //  Console.WriteLine("EXPRESSION To Mutate= " +conjuncts[i]);
          
          // Keep all other expersions the same
          Expression remainder; 
          if(i > 0){
              remainder = conjuncts[0];
              for (int j = 1; j < conjuncts.Count; j++)
            {
              if(j != i){
                remainder = Expression.CreateAnd(remainder, conjuncts[j]);
              }
            }
          }else{
              remainder = conjuncts[1];
              for (int j = 2; j < conjuncts.Count; j++)
            {
              if(j != i){
                remainder = Expression.CreateAnd(remainder, conjuncts[j]);
              }
          }
          }
          Console.WriteLine("EXPRESSION To KeepSame = " + Printer.ExprToString(remainder));
                        List<ExpressionDepth> mutatedExprs = new List<ExpressionDepth>();


          //   }else{
            // var be = conjuncts[i] as BinaryExpr;
            var be = conjuncts[i];

            Console.WriteLine("conjunt[i] == " + conjuncts[i]);
            IEnumerable<ExpressionDepth> exprs = new List<ExpressionDepth>() {new ExpressionDepth(be,1)};
            
            mutatedExprs =  mutateOneExpressionRevised(program,decl,new ExpressionDepth(be,1));
            ////!!!!!
            // List<ExpressionDepth> remainderTest =  mutateOneExpression(program,decl,new ExpressionDepth(remainder as BinaryExpr,1));
              ////!!!!!
            // combinations.Add(mutatedExprs);
            mutatedExprs.Add(new ExpressionDepth(conjuncts[i],1));
            // if(mutatedExprs.Count == 0){
            //    combinations.Add(new List<ExpressionDepth>(){new ExpressionDepth(conjuncts[i],1)});
            // }else{
              combinations.Add(mutatedExprs);
            // testS.Add(mutatedExprs.Select(x => Printer.ExprToString(x.expr)).ToList());
            
            // }
          //put mutations back together with remainder
          if(!DafnyOptions.O.AllMutations){
            foreach(ExpressionDepth e in mutatedExprs)
            {

            var allTogether = Expression.CreateAnd(remainder, e.expr);
            foreach (var allTgether in logicalMutationSimpleList(remainder,e.expr))
            {
              currentExperssions.Add(new ExpressionDepth(allTgether,1));
              Console.WriteLine("mutated  = " + Printer.ExprToString(allTgether) );

            }
            // currentExperssions.Add(new ExpressionDepth(allTogether,1));
            // Console.WriteLine("mutated  = " + Printer.ExprToString(allTogether) );

            }
          }
        
        }
        }
        */
    if(DafnyOptions.O.AllMutations){
      IEnumerable<IEnumerable<ExpressionDepth>> collections = CartesianProductMutations(combinations);
      List<Expression> mutatedLogicalE = new List<Expression>();
      List<Expression> mutatedLogicalETwo = new List<Expression>();

      foreach (var a in collections)
      {
        var comb = a.ToList();
        if(comb.Count >= 2)
        {
          mutatedLogicalE = logicalMutationSimpleList(comb[0].expr,comb[1].expr);
          // var allTogether = Expression.CreateAnd(comb[0].expr,comb[1].expr);
          // var allTogetherOr = Expression.CreateOr(comb[0].expr,comb[1].expr);
          // mutatedLogicalE.Add(allTogether);
          // mutatedLogicalE.Add(allTogetherOr);
         
          for(var exprI = 2; exprI < comb.Count; exprI++)
          {
            foreach (var mle in mutatedLogicalE)
            {
              mutatedLogicalETwo.AddRange(logicalMutationSimpleList(mle,comb[exprI].expr));
            }
            mutatedLogicalE = mutatedLogicalETwo;
            // allTogether = Expression.CreateAnd(allTogether,comb[exprI].expr);
          }
          mutatedLogicalETwo = new List<Expression>();
            foreach (var newMutations in mutatedLogicalE)
            {
              Console.WriteLine("---> " + Printer.ExprToString(newMutations));
              currentExperssions.Add(new ExpressionDepth(newMutations,1));
            } 
            // Console.WriteLine("---> " + Printer.ExprToString(allTogether));
            // currentExperssions.Add(new ExpressionDepth(allTogether,1));
        }
    }
  

  // var allTogether = Expression.CreateAnd(remainder, e.expr);
}

        currentExperssions.Add(new ExpressionDepth(trueExpr,1));
        currentExperssions.Add(new ExpressionDepth(falseExpr,1));
        return currentExperssions;
    }

public List<Expression> logicalMutationSimpleList(Expression a,Expression b)
{
  List<Expression> mutatedEs = new List<Expression>();
  Expression eAnd = Expression.CreateAnd(a,b);
  Expression eOr = Expression.CreateOr(a,b);
  mutatedEs.Add(eAnd);
  mutatedEs.Add(eOr);
  return mutatedEs;
}

public  IEnumerable<IEnumerable<ExpressionDepth>> CartesianProductMutations(
    IEnumerable<IEnumerable<ExpressionDepth>> sequences)
{
    var accum = new List<ExpressionDepth[]>();
    var list = sequences.ToList();
    if (list.Count > 0)
    {
        var enumStack = new Stack<IEnumerator<ExpressionDepth>>();
        var itemStack = new Stack<ExpressionDepth>();
        int index = list.Count - 1;
        var enumerator = list[index].GetEnumerator();
        while (true)
            if (enumerator.MoveNext())
            {
                itemStack.Push(enumerator.Current);
                if (index == 0)
                {
                    accum.Add(itemStack.ToArray());
                    itemStack.Pop();
                }
                else
                {
                    enumStack.Push(enumerator);
                    enumerator = list[--index].GetEnumerator();
                }
            }
            else
            {
                if (++index == list.Count)
                    break;
                itemStack.Pop();
                enumerator = enumStack.Pop();
            }
    }
    return accum;
}

    public List<ExpressionDepth> mutatePredidateHelper(Program program, MemberDecl decl, IEnumerable<ExpressionDepth> expressions){
        List<ExpressionDepth> currentExperssions = new List<ExpressionDepth>();
        var desiredFunction = decl as Function;
        var equalExprToCheck = desiredFunction.Body;
        return getMutatedExprs(program,desiredFunction,equalExprToCheck);
    }

    

    public List<ExpressionDepth> addForAllMutations(Program program, MemberDecl decl, IEnumerable<ExpressionDepth> expressions)
    {
        var desiredFunction = decl as Function;
        var equalExprToCheck = desiredFunction.Body;
       var e = equalExprToCheck as ForallExpr;
       List<ExpressionDepth> currentExperssions = new List<ExpressionDepth>();
          // Console.WriteLine(" ForallExpr = " + e.LogicalBody());
          // Console.WriteLine(" ForallExpr Range= " + Printer.ExprToString(e.Range));
          Console.WriteLine(" ForallExpr Term= " + Printer.ExprToString(e.Term));
          List<Expression> conjuncts = Expression.Conjuncts(e.Term as BinaryExpr).ToList();
          Console.WriteLine("HERE 1-> "+ conjuncts.Count);
          var be = e.LogicalBody() as BinaryExpr;
          // Console.WriteLine("HERE Forall-> "+ Printer.ExprToString(be));
          currentExperssions = getMutatedExprs(program,desiredFunction,e.Term as BinaryExpr);
          List<ExpressionDepth> forallExprs = new List<ExpressionDepth>();
          foreach (ExpressionDepth ee in currentExperssions){
            QuantifierExpr q;
                  ResolvedCloner cloner = new ResolvedCloner();
              var newVars = e.BoundVars.ConvertAll(cloner.CloneBoundVar);

            q = new ForallExpr(e.tok, e.BodyEndTok, newVars, e.Range, ee.expr, e.Attributes);
            // ee = q;
            forallExprs.Add(new ExpressionDepth(q,1));
          }
          return forallExprs;
    }

    public List<ExpressionDepth> addExistsMutations(Program program, MemberDecl decl, IEnumerable<ExpressionDepth> expressions)
    {
      List<ExpressionDepth> currentExperssions = new List<ExpressionDepth>();
      var desiredFunction = decl as Function;
      var equalExprToCheck = desiredFunction.Body;
      var e = equalExprToCheck as ExistsExpr;
      Console.WriteLine(" exists Term= " + Printer.ExprToString(e.Term));
      List<Expression> conjuncts = Expression.Conjuncts(e.Term as BinaryExpr).ToList();
      var be = e.LogicalBody() as BinaryExpr;
      currentExperssions = getMutatedExprs(program,desiredFunction,e.Term as BinaryExpr);
                List<ExpressionDepth> existsExpr = new List<ExpressionDepth>();

      foreach (ExpressionDepth ee in currentExperssions){
        ExistsExpr q;
              ResolvedCloner cloner = new ResolvedCloner();
          var newVars = e.BoundVars.ConvertAll(cloner.CloneBoundVar);

        q = new ExistsExpr(e.tok, e.BodyEndTok, newVars, e.Range, ee.expr, e.Attributes);
        // ee = q;
        existsExpr.Add(new ExpressionDepth(q,1));
      }
          return existsExpr;
    }


public void CalcDepthOneAvailableExpresssions(Program program, MemberDecl decl, IEnumerable<ExpressionDepth> expressions) {
      Contract.Requires(availableExpressions.Count == 0);
      Dictionary<string, HashSet<ExpressionDepth>> typeToExpressionDict = GetRawExpressions(program, decl, expressions, false);

      var trueExpr = Expression.CreateBoolLiteral(decl.tok, true);
      availableExpressions.Add(new ExpressionDepth(trueExpr, 1));
      foreach (var k in typeToExpressionDict.Keys) {
        var values = typeToExpressionDict[k].ToList();
        if (k == "_questionMark_") {
          foreach (var expr in values) {
            // No change to the type, add as is
            availableExpressions.Add(expr);
          }
        } else {
          for (int i = 0; i < values.Count; i++) {
            if (k == "bool") {
              availableExpressions.Add(new ExpressionDepth(values[i].expr, values[i].depth));
              continue;
            }
            for (int j = i + 1; j < values.Count; j++) {
              if (values[i].expr is LiteralExpr && values[j].expr is LiteralExpr) {
                continue;
              }
              if (values[i].expr is ApplySuffix && values[j].expr is ApplySuffix) {
                continue;
              }
              // Equality
              {
                var equalityExpr = Expression.CreateEq(values[i].expr, values[j].expr, values[i].expr.Type);
                equalityExpr.HasCardinality = values[i].expr.HasCardinality | values[j].expr.HasCardinality;
                // TODO(armin): should this be max or addition?
                availableExpressions.Add(new ExpressionDepth(equalityExpr, Math.Max(values[i].depth, values[j].depth)));
              }
              if (values[i].expr is ApplySuffix || values[j].expr is ApplySuffix) {
                continue;
              }
              // Non-Equality
              {
                var neqExpr = Expression.CreateNot(values[i].expr.tok, Expression.CreateEq(values[i].expr, values[j].expr, values[i].expr.Type));
                neqExpr.HasCardinality = values[i].expr.HasCardinality | values[j].expr.HasCardinality;
                availableExpressions.Add(new ExpressionDepth(neqExpr, Math.Max(values[i].depth, values[j].depth)));
                negateOfExpressionIndex[availableExpressions.Count - 1] = availableExpressions.Count - 2;
                negateOfExpressionIndex[availableExpressions.Count - 2] = availableExpressions.Count - 1;
              }

              // only check < <= => > for int and nat types
              if (k != "int" && k != "nat") {
                continue;
              }
              // Lower than
              {
                var lowerThanExpr = Expression.CreateLess(values[i].expr, values[j].expr);
                lowerThanExpr.HasCardinality = values[i].expr.HasCardinality | values[j].expr.HasCardinality;
                availableExpressions.Add(new ExpressionDepth(lowerThanExpr, Math.Max(values[i].depth, values[j].depth)));
              }
              // Greater Equal = !(Lower than)
              {
                var geExpr = Expression.CreateNot(values[i].expr.tok, Expression.CreateLess(values[i].expr, values[j].expr));
                geExpr.HasCardinality = values[i].expr.HasCardinality | values[j].expr.HasCardinality;
                availableExpressions.Add(new ExpressionDepth(geExpr, Math.Max(values[i].depth, values[j].depth)));
                negateOfExpressionIndex[availableExpressions.Count - 1] = availableExpressions.Count - 2;
                negateOfExpressionIndex[availableExpressions.Count - 2] = availableExpressions.Count - 1;
              }
              // Lower Equal
              {
                var leExpr = Expression.CreateAtMost(values[i].expr, values[j].expr);
                leExpr.HasCardinality = values[i].expr.HasCardinality | values[j].expr.HasCardinality;
                availableExpressions.Add(new ExpressionDepth(leExpr, Math.Max(values[i].depth, values[j].depth)));
              }
              // Greater Than = !(Lower equal)
              {
                var gtExpr = Expression.CreateNot(values[i].expr.tok, Expression.CreateAtMost(values[i].expr, values[j].expr));
                gtExpr.HasCardinality = values[i].expr.HasCardinality | values[j].expr.HasCardinality;
                availableExpressions.Add(new ExpressionDepth(gtExpr, Math.Max(values[i].depth, values[j].depth)));
                negateOfExpressionIndex[availableExpressions.Count - 1] = availableExpressions.Count - 2;
                negateOfExpressionIndex[availableExpressions.Count - 2] = availableExpressions.Count - 1;
              }
            }
          }
        }
      }
      numberOfSingleExpr = availableExpressions.Count;
      if (DafnyOptions.O.HoleEvaluatorDepth > 1) {
        for (int i = 0; i < numberOfSingleExpr; i++) {
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
        }
      }
    }

    public void CalcNextDepthAvailableExpressions() {
      // Until here, we only check depth 1 of expressions.
      // Now we try to check next depths
      var tmp = availableExpressions.Count;
      for (int i = prevDepthExprStartIndex; i < tmp; i++) {
        for (int j = 1; j < numberOfSingleExpr; j++) {
          if (IsGoodExprCombinationToExecute(i, j)) {
            var exprDepthA = availableExpressions[i];
            var exprDepthB = availableExpressions[j];
            var exprA = exprDepthA.expr;
            var exprB = exprDepthA.expr;
            var conjunctExpr = Expression.CreateAnd(exprA, exprB);
            conjunctExpr.HasCardinality = exprA.HasCardinality | exprB.HasCardinality;
            BitArray bitArray = new BitArray(bitArrayList[i]);
            bitArray.Or(bitArrayList[j]);
            bitArrayList.Add(bitArray);
            currCombinations.Add(ToBitString(bitArray, true));
            bitArrayStringToIndex[ToBitString(bitArray, true)] = bitArrayList.Count - 1;
            availableExpressions.Add(new ExpressionDepth(conjunctExpr, Math.Max(exprDepthA.depth, exprDepthB.depth)));
          }
        }
      }
      prevDepthExprStartIndex = tmp;
      return;
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

    public static IEnumerable<Expression> ListConstructors(
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
        var applySuffixExpr = new ApplySuffix(ctor.tok, null, new NameSegment(ctor.tok, ctor.Name, null), bindings, null);
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

    public static List<Expression> GetAllPossibleConstructors(Program program,
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

    public static IEnumerable<Expression> ListInvocations(
        Function func,
        Dictionary<string, List<Expression>> typeToExpressionDict,
        List<Expression> arguments,
        int shouldFillIndex) {
      if (shouldFillIndex == func.Formals.Count) {
        List<ActualBinding> bindings = new List<ActualBinding>();
        foreach (var arg in arguments) {
          bindings.Add(new ActualBinding(null, arg));
        }
        var funcCallExpr = new FunctionCallExpr(func.tok, func.FullDafnyName, new ImplicitThisExpr(func.tok), func.tok, func.tok, bindings);
        funcCallExpr.Type = func.ResultType;
        yield return funcCallExpr;
        yield break;
      }
      var t = func.Formals[shouldFillIndex].Type;
      if (typeToExpressionDict.ContainsKey(t.ToString())) {
        foreach (var expr in typeToExpressionDict[t.ToString()]) {
          arguments.Add(expr);
          foreach (var ans in ListInvocations(func, typeToExpressionDict, arguments, shouldFillIndex + 1)) {
            yield return ans;
          }
          arguments.RemoveAt(arguments.Count - 1);
        }
      }
    }

    public static List<ExpressionDepth> GetAllPossibleFunctionInvocations(Program program,
        Function func,
        Dictionary<string, HashSet<ExpressionDepth>> typeToExpressionDict) {
      List<ExpressionDepth> result = new List<ExpressionDepth>();
      List<ExpressionDepth> workingList = new List<ExpressionDepth>();
      foreach (var expr in ListFunctionInvocations(func, typeToExpressionDict, workingList, 0)) {
        result.Add(expr);
      }
      return result;
    }

public static IEnumerable<ExpressionDepth> ListPredicateInvocations(
        Predicate func,
        Dictionary<string, HashSet<ExpressionDepth>> typeToExpressionDict,
        List<ExpressionDepth> arguments,
        int shouldFillIndex) {
      if (shouldFillIndex == func.Formals.Count) {
        List<ActualBinding> bindings = new List<ActualBinding>();
        var depth = 0;
        foreach (var arg in arguments) {
          bindings.Add(new ActualBinding(null, arg.expr));
          depth = Math.Max(depth, arg.depth);
        }
        var applySuffixExpr = new ApplySuffix(func.tok, null, new IdentifierExpr(func.tok, func.FullDafnyName), bindings,null);
        applySuffixExpr.Type = func.ResultType;
        yield return new ExpressionDepth(applySuffixExpr, depth);
        yield break;
      }
      var t = func.Formals[shouldFillIndex].Type;
      if (typeToExpressionDict.ContainsKey(t.ToString())) {
        foreach (var expr in typeToExpressionDict[t.ToString()]) {
          arguments.Add(expr);
          foreach (var ans in ListPredicateInvocations(func, typeToExpressionDict, arguments, shouldFillIndex + 1)) {
            yield return ans;
          }
          arguments.RemoveAt(arguments.Count - 1);
        }
      }
    }

    public static HashSet<ExpressionDepth> GetAllPossiblePredicateInvocations(Program program,
        Predicate func,
        Dictionary<string, HashSet<ExpressionDepth>> typeToExpressionDict) {
      HashSet<ExpressionDepth> result = new HashSet<ExpressionDepth>();
      List<ExpressionDepth> workingList = new List<ExpressionDepth>();
      foreach (var expr in ListPredicateInvocations(func, typeToExpressionDict, workingList, 0)) {
        result.Add(expr);
      }
      return result;
    }

    public IEnumerable<ExpressionDepth> ListArguments(Program program, Function func) {
      foreach (var formal in func.Formals) {
        // Console.WriteLine($"\n{formal.Name}\t{formal.Type.ToString()}");
        // Console.WriteLine(formal.Type.NormalizeExpand().IsTopLevelTypeWithMembers);
        // var c = 0;
        var identExpr = Expression.CreateIdentExpr(formal);
        foreach (var expr in TraverseFormal(program, new ExpressionDepth(identExpr, 1))) {
          // Console.WriteLine($"{c} {variable.Name,-20}:\t{variable.Type}");
          // c++;
          yield return expr;
        }

      }
    }

    public IEnumerable<ExpressionDepth> ListArguments(Program program, Lemma lemma) {
      foreach (var formal in lemma.Ins) {
        var identExpr = Expression.CreateIdentExpr(formal);
        foreach (var expr in TraverseFormal(program, new ExpressionDepth(identExpr, 1))) {
          yield return expr;
        }
      }
      foreach (var formal in lemma.Outs) {
        var identExpr = Expression.CreateIdentExpr(formal);
        foreach (var expr in TraverseFormal(program, new ExpressionDepth(identExpr, 1))) {
          yield return expr;
        }
      }
    }

    public IEnumerable<ExpressionDepth> ListArguments(Program program, Method method) {
      foreach (var formal in method.Ins) {
        var identExpr = Expression.CreateIdentExpr(formal);
        foreach (var expr in TraverseFormal(program, new ExpressionDepth(identExpr, 1))) {
          yield return expr;
        }
      }
      foreach (var formal in method.Outs) {
        var identExpr = Expression.CreateIdentExpr(formal);
        foreach (var expr in TraverseFormal(program, new ExpressionDepth(identExpr, 1))) {
          yield return expr;
        }
      }
    }

    public IEnumerable<ExpressionDepth> ListArgumentsMethodReq(Program program, Method method) {
      foreach (var re in method.Req)
      {
        foreach (var expr in TraverseFormal(program, new ExpressionDepth(re.E, 1))) {
          yield return expr;
        }
      }
    }

    public IEnumerable<ExpressionDepth> ListArgumentsCustom(Program program, Expression e) 
    {
      foreach (var expr in TraverseFormal(program, new ExpressionDepth(e, 1))) {
          yield return expr;
        }
    }
    
public IEnumerable<ExpressionDepth> TraverseFormalSimplified(Program program, ExpressionDepth exprDepth) {
      Contract.Requires(exprDepth != null);
      var maxExpressionDepth = DafnyOptions.O.HoleEvaluatorExpressionDepth;
      if (exprDepth.depth > maxExpressionDepth)
        yield break;
      yield return exprDepth;
      var expr = exprDepth.expr;
      var t = expr.Type;
      if (t is BoolType || t is CharType || t is IntType || t is BigOrdinalType ||
          t is RealType || t is BitvectorType || t is CollectionType) {
        if (t is BoolType) {
          // var trueLiteralExpr = Expression.CreateBoolLiteral(expr.tok, true);
          yield return new ExpressionDepth(expr, 1);
          // NOTE: No need to add false literal since we also check for non-equality.
        } else if (t is IntType) {
          // var zeroLiteralExpr = Expression.CreateIntLiteral(expr.tok, 0);
          yield return new ExpressionDepth(expr, 1);
          // var oneLiteralExpr = Expression.CreateIntLiteral(expr.tok, 1);
          // yield return new ExpressionDepth(oneLiteralExpr, 1);
          
          // if (exprDepth.depth + 1 <= maxExpressionDepth) {
          //   var plusOneLiteralExpr = Expression.CreateIncrement(expr, 1);
          //   yield return new ExpressionDepth(plusOneLiteralExpr, exprDepth.depth + 1);
          //   var minusOneLiteralExpr = Expression.CreateDecrement(expr, 1);
          //   yield return new ExpressionDepth(minusOneLiteralExpr, exprDepth.depth + 1);
          // }
        } else if (t is CollectionType) {
          // create cardinality
          if (exprDepth.depth + 1 <= maxExpressionDepth) {
            var cardinalityExpr = Expression.CreateCardinality(expr, program.BuiltIns);
            yield return new ExpressionDepth(cardinalityExpr, exprDepth.depth + 1);
          }
          if (t is SeqType) {
            var zeroLiteralExpr = Expression.CreateIntLiteral(expr.tok, 0);
            var zerothElement = new SeqSelectExpr(expr.tok, true, expr, zeroLiteralExpr, null, null);
            var st = t as SeqType;
            zerothElement.Type = st.Arg;
            foreach (var e in TraverseFormalSimplified(program, new ExpressionDepth(zerothElement, exprDepth.depth + 1))) {
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
        // Console.WriteLine($"{Printer.ExprToString(td.Constraint)} {td.Var.Name} {td.BaseType} {td.BaseType is IntType}");
        // TODO possibly figure out other expressions from td.Constraint
        if (td.BaseType is IntType) {
          var zeroLiteralExpr = Expression.CreateIntLiteral(expr.tok, 0);
          zeroLiteralExpr.Type = t;
          // TODO Add the literal for maximum value of this newtype decl.
          yield return new ExpressionDepth(zeroLiteralExpr, 1);
          var oneLiteralExpr = Expression.CreateIntLiteral(expr.tok, 1);
          oneLiteralExpr.Type = t;
          yield return new ExpressionDepth(oneLiteralExpr, 1);

          if (exprDepth.depth + 1 <= maxExpressionDepth) {
            var plusOneLiteralExpr = Expression.CreateIncrement(expr, 1);
            plusOneLiteralExpr.Type = t;
            yield return new ExpressionDepth(plusOneLiteralExpr, exprDepth.depth + 1);
            var minusOneLiteralExpr = Expression.CreateDecrement(expr, 1);
            minusOneLiteralExpr.Type = t;
            yield return new ExpressionDepth(minusOneLiteralExpr, exprDepth.depth + 1);
          }
        } else {
          yield return exprDepth;
          // throw new NotImplementedException();
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
        // Console.WriteLine($"{Printer.ExprToString(expr)}");
        var td = (SubsetTypeDecl)cl;
        // Console.WriteLine($"{Printer.ExprToString(td.Constraint)} {td.Var.Name} {td.Rhs}");
        if (td.Rhs is IntType) {
          var zeroLiteralExpr = Expression.CreateIntLiteral(expr.tok, 0);
          zeroLiteralExpr.Type = t;
          yield return new ExpressionDepth(zeroLiteralExpr, 1);
          var oneLiteralExpr = Expression.CreateIntLiteral(expr.tok, 1);
          oneLiteralExpr.Type = t;
          yield return new ExpressionDepth(oneLiteralExpr, 1);
          if (exprDepth.depth + 1 <= maxExpressionDepth) {
            var plusOneLiteralExpr = Expression.CreateIncrement(expr, 1);
            plusOneLiteralExpr.Type = t;
            yield return new ExpressionDepth(plusOneLiteralExpr, exprDepth.depth + 1);
            var minusOneLiteralExpr = Expression.CreateDecrement(expr, 1);
            minusOneLiteralExpr.Type = t;
            yield return new ExpressionDepth(minusOneLiteralExpr, exprDepth.depth + 1);
          }
        }
        // Console.WriteLine($"{variable.Name} is SubsetTypeDecl");
      } else if (cl is ClassDecl) {
        // Console.WriteLine($"{variable.Name} is ClassDecl");
        // TODO traverse underlying definition as well.
        throw new NotImplementedException();
      } else if (cl is DatatypeDecl) {
        if (exprDepth.depth + 1 <= maxExpressionDepth) {
          var dt = (DatatypeDecl)cl;
          var subst = Resolver.TypeSubstitutionMap(dt.TypeArgs, udt.TypeArgs);
          // Console.WriteLine($"{variable.Name} is DatatypeDecl");
          foreach (var ctor in dt.Ctors) {
            if (dt.Ctors.Count > 1) {
              var exprDot = new ExprDotName(ctor.tok, expr, ctor.tok.val + "?", null);
              exprDot.Type = Type.Bool;
              yield return new ExpressionDepth(exprDot, exprDepth.depth + 1);
            }
            foreach (var formal in ctor.Formals) {
              // Console.WriteLine($"type={formal.Type} => {Resolver.SubstType(formal.Type, subst)}");
              // var convertedFormal = new Formal(formal.tok, formal.Name, 
              //     Resolver.SubstType(formal.Type, subst), formal.InParam, formal.IsGhost,
              //     formal.DefaultValue, formal.IsOld, formal.IsNameOnly, formal.NameForCompilation);
              // var identExpr = Expression.CreateIdentExpr(convertedFormal);
              var exprDot = new ExprDotName(formal.tok, expr, formal.tok.val, null);
              exprDot.Type = Resolver.SubstType(formal.Type, subst);
              foreach (var v in TraverseFormalSimplified(program, new ExpressionDepth(exprDot, exprDepth.depth + 1))) {
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
      //   TraverseFormalSimplified(subexpr);
      // }
      // }
    }

    public IEnumerable<ExpressionDepth> TraverseFormal(Program program, ExpressionDepth exprDepth) {
      Contract.Requires(exprDepth != null);
      var maxExpressionDepth = DafnyOptions.O.HoleEvaluatorExpressionDepth;
      if (exprDepth.depth > maxExpressionDepth)
        yield break;
      yield return exprDepth;
      var expr = exprDepth.expr;
      var t = expr.Type;
      if (t is BoolType || t is CharType || t is IntType || t is BigOrdinalType ||
          t is RealType || t is BitvectorType || t is CollectionType) {
        if (t is BoolType) {
          var trueLiteralExpr = Expression.CreateBoolLiteral(expr.tok, true);
          yield return new ExpressionDepth(trueLiteralExpr, 1);
          // NOTE: No need to add false literal since we also check for non-equality.
        } else if (t is IntType) {
          var zeroLiteralExpr = Expression.CreateIntLiteral(expr.tok, 0);
          yield return new ExpressionDepth(zeroLiteralExpr, 1);
          var oneLiteralExpr = Expression.CreateIntLiteral(expr.tok, 1);
          yield return new ExpressionDepth(oneLiteralExpr, 1);
          
          if (exprDepth.depth + 1 <= maxExpressionDepth) {
            var plusOneLiteralExpr = Expression.CreateIncrement(expr, 1);
            yield return new ExpressionDepth(plusOneLiteralExpr, exprDepth.depth + 1);
            var minusOneLiteralExpr = Expression.CreateDecrement(expr, 1);
            yield return new ExpressionDepth(minusOneLiteralExpr, exprDepth.depth + 1);
          }
        } else if (t is CollectionType) {
          // create cardinality
          if (exprDepth.depth + 1 <= maxExpressionDepth) {
            var cardinalityExpr = Expression.CreateCardinality(expr, program.BuiltIns);
            yield return new ExpressionDepth(cardinalityExpr, exprDepth.depth + 1);
          }
          if (t is SeqType) {
            var zeroLiteralExpr = Expression.CreateIntLiteral(expr.tok, 0);
            var zerothElement = new SeqSelectExpr(expr.tok, true, expr, zeroLiteralExpr, null, null);
            var st = t as SeqType;
            zerothElement.Type = st.Arg;
            foreach (var e in TraverseFormal(program, new ExpressionDepth(zerothElement, exprDepth.depth + 1))) {
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
        // Console.WriteLine($"{Printer.ExprToString(td.Constraint)} {td.Var.Name} {td.BaseType} {td.BaseType is IntType}");
        // TODO possibly figure out other expressions from td.Constraint
        if (td.BaseType is IntType) {
          var zeroLiteralExpr = Expression.CreateIntLiteral(expr.tok, 0);
          zeroLiteralExpr.Type = t;
          // TODO Add the literal for maximum value of this newtype decl.
          yield return new ExpressionDepth(zeroLiteralExpr, 1);
          var oneLiteralExpr = Expression.CreateIntLiteral(expr.tok, 1);
          oneLiteralExpr.Type = t;
          yield return new ExpressionDepth(oneLiteralExpr, 1);

          if (exprDepth.depth + 1 <= maxExpressionDepth) {
            var plusOneLiteralExpr = Expression.CreateIncrement(expr, 1);
            plusOneLiteralExpr.Type = t;
            yield return new ExpressionDepth(plusOneLiteralExpr, exprDepth.depth + 1);
            var minusOneLiteralExpr = Expression.CreateDecrement(expr, 1);
            minusOneLiteralExpr.Type = t;
            yield return new ExpressionDepth(minusOneLiteralExpr, exprDepth.depth + 1);
          }
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
        // Console.WriteLine($"{Printer.ExprToString(expr)}");
        var td = (SubsetTypeDecl)cl;
        // Console.WriteLine($"{Printer.ExprToString(td.Constraint)} {td.Var.Name} {td.Rhs}");
        if (td.Rhs is IntType) {
          var zeroLiteralExpr = Expression.CreateIntLiteral(expr.tok, 0);
          zeroLiteralExpr.Type = t;
          yield return new ExpressionDepth(zeroLiteralExpr, 1);
          var oneLiteralExpr = Expression.CreateIntLiteral(expr.tok, 1);
          oneLiteralExpr.Type = t;
          yield return new ExpressionDepth(oneLiteralExpr, 1);
          if (exprDepth.depth + 1 <= maxExpressionDepth) {
            var plusOneLiteralExpr = Expression.CreateIncrement(expr, 1);
            plusOneLiteralExpr.Type = t;
            yield return new ExpressionDepth(plusOneLiteralExpr, exprDepth.depth + 1);
            var minusOneLiteralExpr = Expression.CreateDecrement(expr, 1);
            minusOneLiteralExpr.Type = t;
            yield return new ExpressionDepth(minusOneLiteralExpr, exprDepth.depth + 1);
          }
        }
        // Console.WriteLine($"{variable.Name} is SubsetTypeDecl");
      } else if (cl is ClassDecl) {
        // Console.WriteLine($"{variable.Name} is ClassDecl");
        // TODO traverse underlying definition as well.
        throw new NotImplementedException();
      } else if (cl is DatatypeDecl) {
        if (exprDepth.depth + 1 <= maxExpressionDepth) {
          var dt = (DatatypeDecl)cl;
          var subst = Resolver.TypeSubstitutionMap(dt.TypeArgs, udt.TypeArgs);
          // Console.WriteLine($"{variable.Name} is DatatypeDecl");
          foreach (var ctor in dt.Ctors) {
            if (dt.Ctors.Count > 1) {
              var exprDot = new ExprDotName(ctor.tok, expr, ctor.tok.val + "?", null);
              exprDot.Type = Type.Bool;
              yield return new ExpressionDepth(exprDot, exprDepth.depth + 1);
            }
            foreach (var formal in ctor.Formals) {
              // Console.WriteLine($"type={formal.Type} => {Resolver.SubstType(formal.Type, subst)}");
              // var convertedFormal = new Formal(formal.tok, formal.Name, 
              //     Resolver.SubstType(formal.Type, subst), formal.InParam, formal.IsGhost,
              //     formal.DefaultValue, formal.IsOld, formal.IsNameOnly, formal.NameForCompilation);
              // var identExpr = Expression.CreateIdentExpr(convertedFormal);
              var exprDot = new ExprDotName(formal.tok, expr, formal.tok.val, null);
              exprDot.Type = Resolver.SubstType(formal.Type, subst);
              foreach (var v in TraverseFormal(program, new ExpressionDepth(exprDot, exprDepth.depth + 1))) {
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
      // Console.WriteLine(t.ToString());
      if (t is BoolType || t is CharType || t is IntType || t is BigOrdinalType ||
          t is RealType || t is BitvectorType || t is CollectionType) {
        // Console.WriteLine("pre-defined type");
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
        // Console.WriteLine($"{t.ToString()} is NewtypeDecl");
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
