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
  public class RevealFinder {

    private ProofEvaluator proofEval = null;

    public RevealFinder(ProofEvaluator proofEval) {
      this.proofEval = proofEval;
    }

    public Dictionary<string, List<Expression>> GetTypeToExpressionDict(IEnumerable<Expression> expressionList) {
      Dictionary<string, List<Expression>> typeToExpressionDict = new Dictionary<string, List<Expression>>();
      foreach (var expr in expressionList) {
        var exprString = Printer.ExprToString(expr);
        var typeString = expr.Type.ToString();
        // Console.WriteLine($"{c,2} {exprString,-20} {typeString}");
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
      return typeToExpressionDict;
    }

    private bool IsOpaque(Attributes attrs) {
      if (attrs == null) {
        return false;
      }
      if (attrs.Name == "opaque") {
        return true;
      }
      else return IsOpaque(attrs.Prev);
    }

    public List<Statement> GetRevealStatements(Program program) {
      var result = new List<Statement>();
      foreach (var kvp in program.ModuleSigs) {
        foreach (var d in kvp.Value.ModuleDef.TopLevelDecls) {
          var cl = d as TopLevelDeclWithMembers;
          if (cl != null) {
            foreach (var member in cl.Members) {
              if (member is Lemma && member.ToString() == "NextPreservesAgreementChosenInv")
              {
                Console.WriteLine(member.ToString());
              }
              if (member is Function) {
                if (IsOpaque(member.Attributes)) {
                  List<Expression> lhss = new List<Expression>();
                  List<AssignmentRhs> rhss = new List<AssignmentRhs>();
                  // lhss.Add(new IdentifierExpr(member.tok, $"temp_{cnt}_${i}"));
                  rhss.Add(new ExprRhs(new ApplySuffix(member.tok, null, new NameSegment(member.tok, $"reveal_{member.ToString()}", new List<Type>()), new List<ActualBinding>(), member.tok)));
                  UpdateStmt updateStmt = new UpdateStmt(member.tok, member.tok, lhss, rhss);
                  result.Add(updateStmt);
                  Console.WriteLine(Printer.StatementToString(updateStmt));
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
      return result;
    }
  }
}