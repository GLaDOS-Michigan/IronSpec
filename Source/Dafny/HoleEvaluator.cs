//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------
using System;
using System.IO;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Reflection;
using Microsoft.Boogie;

namespace Microsoft.Dafny {

  public class HoleEvaluator {

    public static void Evaluate(Program program, string funcName)
    {
      // Console.WriteLine($"hole evaluation begins for func {funcName}");
      foreach (var kvp in program.ModuleSigs) {
        var c = 0;
        // iterate over all functions / predicates (this doesn't include lemmas)
        foreach (var topLevelDecl in ModuleDefinition.AllFunctions(kvp.Value.ModuleDef.TopLevelDecls)) {
          // Console.WriteLine($"{c} {topLevelDecl.FullDafnyName}");
          if (topLevelDecl.FullDafnyName == funcName) {
            Console.WriteLine("Found desired function.");
            ListArguments(topLevelDecl);
          }
          c++;
        }
      }
    }

    public static void ListArguments(Function func)
    {
      foreach (var formal in func.Formals) {
        Console.WriteLine($"{formal.Name}\t{formal.Type.ToString()}");
        // Console.WriteLine(formal.Type.NormalizeExpand().IsTopLevelTypeWithMembers);
        var c = 0;
        Console.WriteLine(formal.DefaultValue);
        foreach (var expr in TraverseFormal(Expression.CreateIdentExpr(formal)))
        {
          Console.WriteLine($"{c} {Printer.ExprToString(expr)}:{expr.Type}");
          c++;
        }
      }
    }

    public static IEnumerable<Expression> TraverseFormal(Expression expr)
    {
      Contract.Requires(expr != null);
      yield return expr;
      var members = expr.Type.NormalizeExpand().AsTopLevelTypeWithMembers;
      foreach(var mem in members.Members)
      {
        Console.WriteLine(mem);
      }
      // if (expr.SubExpressions != null)
      // {
        foreach (var subexpr in expr.SubExpressions)
        {
          TraverseFormal(subexpr);
        }
      // }
    }

  }
}