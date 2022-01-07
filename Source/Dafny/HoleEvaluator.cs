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
        // iterate over all functions / predicates (this doesn't include lemmas)
        foreach (var topLevelDecl in ModuleDefinition.AllFunctions(kvp.Value.ModuleDef.TopLevelDecls)) {
          // Console.WriteLine($"{c} {topLevelDecl.FullDafnyName}");
          if (topLevelDecl.FullDafnyName == funcName) {
            Console.WriteLine("Found desired function.");
            var expressions = ListArguments(program, topLevelDecl);
            var c = 0;
            foreach (var expr in expressions) {
              c++;
              Console.WriteLine($"{c,2} {expr} {expr.tok.val} !!{expr.Type}");
              if (expr is ExprDotName) {
                var edt = expr as ExprDotName;
                Console.WriteLine($"   {edt.Lhs} {edt.Lhs.tok.val}");
              }
              // AddExpression(program, topLevelDecl, expr);
            }
          }
        }
      }
    }

    // public static void AddExpression(Program program, Function func)
    // {
    //   foreach(var expr in Expression.Conjuncts(func.Body)) {
    //     Console.WriteLine($"{expr.tok.val}");
    //   }
    // }

    public static IEnumerable<Expression> ListArguments(Program program, Function func)
    {
      foreach (var formal in func.Formals) {
        // Console.WriteLine($"\n{formal.Name}\t{formal.Type.ToString()}");
        // Console.WriteLine(formal.Type.NormalizeExpand().IsTopLevelTypeWithMembers);
        // var c = 0;
        var identExpr = Expression.CreateIdentExpr(formal);
        foreach (var expr in TraverseFormal(program, identExpr))
        {
          // Console.WriteLine($"{c} {variable.Name,-20}:\t{variable.Type}");
          // c++;
          yield return expr;
        }

      }
    }

    public static IEnumerable<Expression> TraverseFormal(Program program, Expression expr)
    {
      Contract.Requires(expr != null);
      yield return expr;
      var t = expr.Type;
      if (t is BoolType || t is CharType || t is IntType || t is BigOrdinalType ||
          t is RealType || t is BitvectorType || t is CollectionType) {
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
        // Console.WriteLine($"{variable.Name} is NewtypeDecl");
        foreach (var v in TraverseType(program, td.BaseType))
        {
          // var ngv = (Formal)variable;
          // var dotVar = new Formal(ngv.tok, ngv.Name + "." + v.Name, v.Type, true, true, null);
          var e = new ExprDotName(v, expr, v.val, null);
          e.Type = expr.Type;
          // Console.WriteLine($"Constructing dot var:{dotVar.Name}");
          yield return e;
        }
      } else if (cl is SubsetTypeDecl) {
        var td = (SubsetTypeDecl)cl;
        // Console.WriteLine($"{variable.Name} is SubsetTypeDecl");
        // TODO traverse underlying definition as well.
      } else if (cl is ClassDecl) {
        // Console.WriteLine($"{variable.Name} is ClassDecl");
        // TODO traverse underlying definition as well.
      } else if (cl is DatatypeDecl) {
        var dt = (DatatypeDecl)cl;
        var subst = Resolver.TypeSubstitutionMap(dt.TypeArgs, udt.TypeArgs);
        // Console.WriteLine($"{variable.Name} is DatatypeDecl");
        // Console.WriteLine($"Ctor.Count:{dt.Ctors.Count}");
        foreach (var ctor in dt.Ctors) {
          foreach (var formal in ctor.Formals) {
            // Console.WriteLine(formal.Name);
            // Console.WriteLine($"type={formal.Type} => {Resolver.SubstType(formal.Type, subst)}");
            // var convertedFormal = new Formal(formal.tok, formal.Name, 
            //     Resolver.SubstType(formal.Type, subst), formal.InParam, formal.IsGhost,
            //     formal.DefaultValue, formal.IsOld, formal.IsNameOnly, formal.NameForCompilation);
            // var identExpr = Expression.CreateIdentExpr(convertedFormal);
            var exprDot = new ExprDotName(formal.tok, expr, formal.tok.val, null);
            exprDot.Type = Resolver.SubstType(formal.Type, subst);
            foreach (var v in TraverseFormal(program, exprDot))
            {
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

    public static IEnumerable<IToken> TraverseType(Program program, Type t)
    {
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
        foreach (var v in TraverseType(program, td.BaseType))
        {
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
      }
      else {
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