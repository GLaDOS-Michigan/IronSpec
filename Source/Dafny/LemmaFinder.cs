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
  public class LemmaFinder {

    private ProofEvaluator proofEval = null;

    public LemmaFinder(ProofEvaluator proofEval) {
      this.proofEval = proofEval;
    }

    public List<ExpressionFinder.StatementDepth> GetLemmaStatements(Program program, Dictionary<string, List<ExpressionFinder.ExpressionDepth>> typeToExpressionDict) {
      var result = new List<ExpressionFinder.StatementDepth>();
      foreach (var kvp in program.ModuleSigs) {
        foreach (var d in kvp.Value.ModuleDef.TopLevelDecls) {
          var cl = d as TopLevelDeclWithMembers;
          if (cl != null) {
            foreach (var member in cl.Members) {
              if (member is Lemma) {
                var lemmaExprs = GetAllPossibleLemmaInvocations(program, member as Lemma, typeToExpressionDict);
                Console.WriteLine($"{member.Name} -> {lemmaExprs.Count}");
                foreach (var expr in lemmaExprs) {
                  List<Expression> lhss = new List<Expression>();
                  List<AssignmentRhs> rhss = new List<AssignmentRhs>();
                  // lhss.Add(new IdentifierExpr(member.tok, $"temp_{cnt}_${i}"));
                  rhss.Add(new ExprRhs(expr.expr));
                  UpdateStmt updateStmt = new UpdateStmt(member.tok, member.tok, lhss, rhss);
                  result.Add(new ExpressionFinder.StatementDepth(updateStmt, expr.depth));
                }
                // var exprs = new List<Expression>();
                // var stmt = new RevealStmt(member.BodyStartTok, member.BodyEndTok, exprs);
                // var predicateInvocations = GetAllPossiblePredicateInvocations(program, member as Predicate, typeToExpressionDict);
                // if (!typeToExpressionDict.ContainsKey("bool")) {
                //   typeToExpressionDict.Add("bool", new List<Expression>());
                // }
                // typeToExpressionDict["bool"].AddRange(predicateInvocations);
              }
            }
          }
        }
      }
      Console.WriteLine($"result.size = {result.Count}");
      return result;
    }
    public IEnumerable<ExpressionFinder.ExpressionDepth> ListInvocations(
        Lemma lemma,
        Dictionary<string, List<ExpressionFinder.ExpressionDepth>> typeToExpressionDict,
        List<Expression> arguments,
        int maxDepth,
        int shouldFillIndex) {
      if (shouldFillIndex == lemma.Ins.Count) {
        List<ActualBinding> bindings = new List<ActualBinding>();
        foreach (var arg in arguments) {
          bindings.Add(new ActualBinding(null, arg));
        }
        var lemmaCallExpr = new ApplySuffix(lemma.tok, null, new NameSegment(lemma.tok, lemma.Name, new List<Type>()), bindings, lemma.tok);
        yield return new ExpressionFinder.ExpressionDepth(lemmaCallExpr, maxDepth);
        yield break;
      }
      var t = lemma.Ins[shouldFillIndex].Type;
      if (typeToExpressionDict.ContainsKey(t.ToString())) {
        foreach (var expr in typeToExpressionDict[t.ToString()]) {
          arguments.Add(expr.expr);
          foreach (var ans in ListInvocations(lemma, typeToExpressionDict, arguments, Math.Max(maxDepth, expr.depth), shouldFillIndex + 1)) {
            yield return ans;
          }
          arguments.RemoveAt(arguments.Count - 1);
        }
      }
    }

    public List<ExpressionFinder.ExpressionDepth> GetAllPossibleLemmaInvocations(Program program,
        Lemma lemma,
        Dictionary<string, List<ExpressionFinder.ExpressionDepth>> typeToExpressionDict) {
      List<ExpressionFinder.ExpressionDepth> result = new List<ExpressionFinder.ExpressionDepth>();
      List<Expression> workingList = new List<Expression>();
      foreach (var expr in ListInvocations(lemma, typeToExpressionDict, workingList, 0, 0)) {
        result.Add(expr);
      }
      return result;
    }
  }
}