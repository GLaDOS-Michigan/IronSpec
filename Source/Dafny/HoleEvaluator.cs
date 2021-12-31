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
            ListArguments(program, topLevelDecl);
          }
          c++;
        }
      }
    }

    public static void ListArguments(Program program, Function func)
    {
      foreach (var formal in func.Formals) {
        Console.WriteLine($"\n{formal.Name}\t{formal.Type.ToString()}");
        // Console.WriteLine(formal.Type.NormalizeExpand().IsTopLevelTypeWithMembers);
        var c = 0;
        foreach (var expr in TraverseFormal(program, formal))
        {
          Console.WriteLine($"{c} {expr.Name,-20}:\t{expr.Type}");
          c++;
        }

      }
    }

    public static IEnumerable<IVariable> TraverseFormal(Program program, IVariable variable)
    {
      yield return variable;
      Contract.Requires(variable != null);
      var t = variable.Type;
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
          var ngv = (Formal)variable;
          var dotVar = new Formal(ngv.tok, ngv.Name + "." + v.Name, v.Type, true, true, null);
          // Console.WriteLine($"Constructing dot var:{dotVar.Name}");
          yield return dotVar;
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
            // Console.WriteLine($"type={formal.Type} => {Resolver.SubstType(formal.Type, subst)}");
            var convertedFormal = new Formal(formal.tok, formal.Name, 
                Resolver.SubstType(formal.Type, subst), formal.InParam, formal.IsGhost,
                formal.DefaultValue, formal.IsOld, formal.IsNameOnly, formal.NameForCompilation);
            foreach (var v in TraverseFormal(program, convertedFormal))
            {
              var ngv = (Formal)variable;
              var dotVar = new Formal(ngv.tok, ngv.Name + "." + v.Name, v.Type, true, true, null);
              // Console.WriteLine($"Constructing dot var:{dotVar.Name}");
              yield return dotVar;
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

    public static IEnumerable<IVariable> TraverseType(Program program, Type t)
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