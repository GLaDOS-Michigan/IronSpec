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
using System.Linq;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Diagnostics;
using System.Reflection;
using System.Linq;
using Microsoft.Boogie;
using System.Threading.Tasks;

namespace Microsoft.Dafny {
  public class CodeModifier {
    public CodeModifier() { }

    public static void EraseFromPredicate(Predicate predicate, int line) {
      var exprList = Expression.Conjuncts(predicate.Body).ToList();
      var i = -1;
      for (i = 0; i < exprList.Count; i++) {
        if (line < exprList[i].tok.line) {
          break;
        }
      }
      if (i != exprList.Count) {
        exprList.RemoveAt(i);
      }
      var body = exprList[0];
      for (int j = 1; j < exprList.Count; j++) {
        body = Expression.CreateAnd(body, exprList[j]);
      }
      predicate.Body = body;
    }

    public static string Erase(Program program, string removeFileLine) {
      var name = "";
      var fileLineList = removeFileLine.Split(',');
      foreach (var fileLineString in fileLineList) {
        var fileLineArray = fileLineString.Split(':');
        var file = fileLineArray[0];
        var line = Int32.Parse(fileLineArray[1]);
        if (program.ModuleSigs.Count == 0) {
          // unresolved program
          return "";
        }
        foreach (var kvp in program.ModuleSigs) {
          foreach (var topLevelDecl in ModuleDefinition.AllFunctions(kvp.Value.ModuleDef.TopLevelDecls)) {
            if (Path.GetFullPath(topLevelDecl.tok.filename) == file) {
              if (topLevelDecl.BodyStartTok.line <= line && line <= topLevelDecl.BodyEndTok.line) {
                if (topLevelDecl is Predicate) {
                  if (name != "" && name != topLevelDecl.FullDafnyName) {
                    throw new NotSupportedException("do not support removing from two lemmas at the same time!");
                  }
                  name = topLevelDecl.FullDafnyName;
                  EraseFromPredicate(topLevelDecl as Predicate, line);
                }
              }
            }
          }
          foreach (var topLevelDecl in ModuleDefinition.AllLemmas(kvp.Value.ModuleDef.TopLevelDecls)) {
            if (Path.GetFullPath(topLevelDecl.tok.filename) == file) {
              if (topLevelDecl.BodyStartTok.line <= line && line <= topLevelDecl.BodyEndTok.line) {
                var stmtList = topLevelDecl.Body.Body;
                // Console.WriteLine($"topLevelDecl : {topLevelDecl.FullDafnyName}");
                if (name != "" && name != topLevelDecl.FullDafnyName) {
                  throw new NotSupportedException("do not support removing from two lemmas at the same time!");
                }
                name = topLevelDecl.FullDafnyName;
                var i = -1;
                for (i = 0; i < stmtList.Count; i++) {
                  if (line < stmtList[i].Tok.line) {
                    break;
                  }
                }
                i--;
                if (i != -1 && EraseFromStatement(topLevelDecl.Body.Body[i], line)) {
                  topLevelDecl.Body.Body.RemoveAt(i);
                }
              }
            }
          }
        }
      }
      return name;
    }

    // returns true if statement should also be removed in parent
    private static bool EraseFromStatement(Statement stmt, int line) {
      if (stmt is BlockStmt) {
        EraseFromBlockStmt(stmt as BlockStmt, line);
        return false;
      }
      else if (stmt is IfStmt) {
        EraseFromIfStmt(stmt as IfStmt, line);
        return false;
      }
      else if (stmt is ForallStmt) {
        return EraseFromForallStmt(stmt as ForallStmt, line);
      }
      return true;
    }

    private static void EraseFromBlockStmt(BlockStmt blockStmt, int line) {
      for(int i = 0; i < blockStmt.Body.Count; i++) {
        if (blockStmt.Body[i].Tok.line <= line) {
          if (EraseFromStatement(blockStmt.Body[i], line)) {
            blockStmt.Body.RemoveAt(i);
          }
          return;
        }
      }
    }

    private static void EraseFromIfStmt(IfStmt ifStmt, int line) {
      if (ifStmt.Thn.Tok.line <= line && line <= ifStmt.Thn.EndTok.line) {
        EraseFromBlockStmt(ifStmt.Thn, line);
      }
      else if (ifStmt.Els != null) {
        EraseFromStatement(ifStmt.Els, line);
      }
    }

    private static bool EraseFromForallStmt(ForallStmt forallStmt, int line) {
      if (line < forallStmt.Body.Tok.line) {
        return true;
      }
      else {
        EraseFromStatement(forallStmt.Body, line);
        return false;
      }
    }

    public static void InsertStmtListAtLine(Lemma lemma, List<Statement> stmtList, int lineNo)
    {
      if (lineNo == -1) {
        for (int i = 0; i < stmtList.Count; i++) {
          lemma.Body.Body.Insert(i, stmtList[i]);
        }
      }
      else {
        if (lemma.BodyStartTok.line <= lineNo && lineNo <= lemma.BodyEndTok.line) {
          var lemmaStmtList = lemma.Body.Body;
          if (lemmaStmtList.Count == 0) {
            for (int j = 0; j < stmtList.Count; j++) {
              lemma.Body.Body.Insert(j, stmtList[j]);
            }
          } else {
            var i = -1;
            for (i = 0; i < lemmaStmtList.Count; i++) {
              if (lineNo < lemmaStmtList[i].Tok.line) {
                break;
              }
            }
            // i--;
            if (i == lemmaStmtList.Count) {
              for (int j = 0; j < stmtList.Count; j++) {
                lemma.Body.Body.Insert(stmtList.Count, stmtList[j]);
              }
            }
            else if (InsertIntoStatement(lemma.Body.Body[i], stmtList, lineNo)) {
              for (int j = 0; j < stmtList.Count; j++) {
                lemma.Body.Body.Insert(i + j, stmtList[j]);
              }
            }
          }
        }
      }
    }

    public static bool InsertIntoStatement(Statement stmt, List<Statement> stmtList, int lineNo) {
      if (stmt is BlockStmt) {
        InsertIntoBlockStmt(stmt as BlockStmt, stmtList, lineNo);
        return false;
      }
      else if (stmt is IfStmt) {
        InsertIntoIfStmt(stmt as IfStmt, stmtList, lineNo);
        return false;
      }
      else if (stmt is ForallStmt) {
        return InsertIntoForallStmt(stmt as ForallStmt, stmtList, lineNo);
      }
      return true;
    }

    public static void InsertIntoBlockStmt(BlockStmt blockStmt, List<Statement> stmtList, int lineNo) {
      int i = 0;
      for(i = 0; i < blockStmt.Body.Count; i++) {
        if (lineNo < blockStmt.Body[i].Tok.line) {
          break;
        }
      }
      if (i != 0) {
        if (InsertIntoStatement(blockStmt.Body[i - 1], stmtList, lineNo)) {
          for (int j = 0; j < stmtList.Count; j++) {
            blockStmt.Body.Insert(i + j, stmtList[j]);
          }
        }
      }
      else {
        for (int j = 0; j < stmtList.Count; j++) {
          blockStmt.Body.Insert(j, stmtList[j]);
        }
      }
    }

    private static void InsertIntoIfStmt(IfStmt ifStmt, List<Statement> stmtList, int lineNo) {
      if (ifStmt.Thn.Tok.line <= lineNo && lineNo <= ifStmt.Thn.EndTok.line) {
        InsertIntoBlockStmt(ifStmt.Thn, stmtList, lineNo);
      }
      else if (ifStmt.Els != null) {
        InsertIntoStatement(ifStmt.Els, stmtList, lineNo);
      }
    }

    private static bool InsertIntoForallStmt(ForallStmt forallStmt, List<Statement> stmtList, int lineNo) {
      if (lineNo < forallStmt.Body.Tok.line) {
        return true;
      }
      else {
        InsertIntoStatement(forallStmt.Body, stmtList, lineNo);
        return false;
      }
    }
  }
}