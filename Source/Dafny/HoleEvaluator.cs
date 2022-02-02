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
using System.Diagnostics;
using System.Reflection;
using System.Linq;
using Microsoft.Boogie;

namespace Microsoft.Dafny {

  public class HoleEvaluator {

    public bool Evaluate(Program program, string funcName) {
      // Console.WriteLine($"hole evaluation begins for func {funcName}");
      var foundDesiredFunction = false;
      foreach (var kvp in program.ModuleSigs) {
        // iterate over all functions / predicates (this doesn't include lemmas)
        foreach (var topLevelDecl in ModuleDefinition.AllFunctions(kvp.Value.ModuleDef.TopLevelDecls)) {
          if (topLevelDecl.FullDafnyName == funcName) {
            Console.WriteLine("Found desired function.");
            foundDesiredFunction = true;
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
            Function topLevelDeclCopy = new Function(
              topLevelDecl.tok, topLevelDecl.Name, topLevelDecl.HasStaticKeyword,
              topLevelDecl.IsGhost, topLevelDecl.TypeArgs, topLevelDecl.Formals,
              topLevelDecl.Result, topLevelDecl.ResultType, topLevelDecl.Req,
              topLevelDecl.Reads, topLevelDecl.Ens, topLevelDecl.Decreases,
              topLevelDecl.Body, topLevelDecl.ByMethodTok, topLevelDecl.ByMethodBody,
              topLevelDecl.Attributes, topLevelDecl.SignatureEllipsis);
            // check equality of each pair of same type expressions
            var cnt = 0;
            var trueExpr = Expression.CreateBoolLiteral(topLevelDecl.Body.tok, true);
            PrintExpr(program, topLevelDecl, trueExpr, cnt);
            // using (var wr = new System.IO.StringWriter()) {
            //   var pr = new Printer(wr);
            //   pr.PrintProgram(program, true);
            //   File.WriteAllTextAsync($"/tmp/{funcName}_base.dfy",
            //     Printer.ToStringWithoutNewline(wr));
            // }
            foreach (var k in typeToExpressionDict.Keys) {
              var values = typeToExpressionDict[k];
              if (k == "_questionMark_") {
                for (int i = 0; i < values.Count; i++) {
                  {
                    cnt = cnt + 1;
                    // No change to the type, print as is
                    var expr = values[i];
                    PrintExpr(program, topLevelDecl, expr, cnt);
                    topLevelDecl.Body = topLevelDeclCopy.Body;
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
                      cnt = cnt + 1;
                      var equalityExpr = Expression.CreateEq(values[i], values[j], values[i].Type);
                      var expr = equalityExpr;
                      PrintExpr(program, topLevelDecl, expr, cnt);
                      topLevelDecl.Body = topLevelDeclCopy.Body;
                    }

                    // Non-Equality
                    {
                      cnt = cnt + 1;
                      var neqExpr = Expression.CreateNot(values[i].tok, Expression.CreateEq(values[i], values[j], values[i].Type));
                      var expr = neqExpr;
                      PrintExpr(program, topLevelDecl, expr, cnt);
                      topLevelDecl.Body = topLevelDeclCopy.Body;
                    }

                    if (k == "bool") {
                      continue;
                    }

                    // Lower than
                    {
                      cnt = cnt + 1;
                      var lowerThanExpr = Expression.CreateLess(values[i], values[j]);
                      var expr = lowerThanExpr;
                      PrintExpr(program, topLevelDecl, expr, cnt);
                      topLevelDecl.Body = topLevelDeclCopy.Body;
                    }

                    // Greater Equal = !(Lower than)
                    {
                      cnt = cnt + 1;
                      var geExpr = Expression.CreateNot(values[i].tok, Expression.CreateLess(values[i], values[j]));
                      var expr = geExpr;
                      PrintExpr(program, topLevelDecl, expr, cnt);
                      topLevelDecl.Body = topLevelDeclCopy.Body;
                    }

                    // Lower Equal
                    {
                      cnt = cnt + 1;
                      var leExpr = Expression.CreateAtMost(values[i], values[j]);
                      var expr = leExpr;
                      PrintExpr(program, topLevelDecl, expr, cnt);
                      topLevelDecl.Body = topLevelDeclCopy.Body;
                    }

                    // Greater Than = !(Lower equal)
                    {
                      cnt = cnt + 1;
                      var gtExpr = Expression.CreateNot(values[i].tok, Expression.CreateAtMost(values[i], values[j]));
                      var expr = gtExpr;
                      PrintExpr(program, topLevelDecl, expr, cnt);
                      topLevelDecl.Body = topLevelDeclCopy.Body;
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
      foreach (var p in dafnyProcesses) {
        p.WaitForExit();
      }
      foreach (var p in dafnyProcesses) {
        var cnt = processToCnt[p];
        File.WriteAllTextAsync($"/tmp/output_{funcName}_{cnt}.txt", dafnyOutput[p]);
      }
      var findCorrectAnswer = false;
      foreach (var p in dafnyProcesses) {
        var cnt = processToCnt[p];
        var position = processToLemmaPosition[p];
        var expectedStart =
          $"/tmp/{funcName}_{cnt}.dfy({position + 3},0): Error: A postcondition might not hold on this return path." +
          Environment.NewLine +
          $"/tmp/{funcName}_{cnt}.dfy({position + 2},10): Related location: This is the postcondition that might not hold.";
        var output = dafnyOutput[p];
        if (output.StartsWith(expectedStart) && output.EndsWith("1 error" + Environment.NewLine)) {
          findCorrectAnswer = true;
          // Console.WriteLine(output);
          Console.WriteLine(p.StartInfo.Arguments);
          Console.WriteLine(Printer.ExprToString(processToExpr[p]));
        }
      }
      if (findCorrectAnswer == false) {
        Console.WriteLine("Couldn't find any correct answer. Printing 0 error ones");
        foreach (var p in dafnyProcesses) {
          var output = dafnyOutput[p];
          if (output.EndsWith("0 errors" + Environment.NewLine)) {
            // Console.WriteLine(output);
            Console.WriteLine(p.StartInfo.Arguments);
            Console.WriteLine(Printer.ExprToString(processToExpr[p]));
          }
        }
      }
      return true;
    }

    private Process startProcessWithOutput(string command, string args) {
      Process p = new Process();
      p.StartInfo = new ProcessStartInfo(command, args);
      p.StartInfo.RedirectStandardOutput = true;
      p.StartInfo.RedirectStandardError = false;
      p.StartInfo.UseShellExecute = false;
      p.StartInfo.CreateNoWindow = true;
      p.OutputDataReceived += new DataReceivedEventHandler(DafnyOutputHandler);
      p.Start();
      p.BeginOutputReadLine();

      return p;
    }

    private void DafnyOutputHandler(object sendingProcess,
            DataReceivedEventArgs outLine) {
      // Collect the net view command output.
      if (!String.IsNullOrEmpty(outLine.Data)) {
        // Add the text to the collected output.
        dafnyOutput[sendingProcess as Process] += outLine.Data + Environment.NewLine;
      }
    }

    private Dictionary<Process, string> dafnyOutput = new Dictionary<Process, string>();
    private List<Process> dafnyProcesses = new List<Process>();
    private Dictionary<Process, Expression> processToExpr = new Dictionary<Process, Expression>();
    private Dictionary<Process, int> processToCnt = new Dictionary<Process, int>();
    private Dictionary<Process, int> processToLemmaPosition = new Dictionary<Process, int>();

    public void PrintExpr(Program program, Function func, Expression expr, int cnt) {
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
      Process p = startProcessWithOutput(dafnyBinaryPath,
        $"{args} /tmp/{funcName}_{cnt}.dfy");
      dafnyProcesses.Add(p);
      processToExpr[p] = expr;
      processToCnt[p] = cnt;
      processToLemmaPosition[p] = lemmaForExprValidityPosition;
      dafnyOutput[p] = "";

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