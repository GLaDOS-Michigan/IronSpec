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

  public class HoleFinder {
    private string UnderscoreStr = "";
    private static Random random = new Random();

    public static string RandomString(int length) {
      const string chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";
      return new string(Enumerable.Repeat(chars, length)
          .Select(s => s[random.Next(s.Length)]).ToArray());
    }

    private HoleFinderExecutor holeFinderExecutor = new HoleFinderExecutor();

    public HoleFinder() { }

    public void PrintWithFuncFalse(Program program, Function func) {
      var funcName = func.FullDafnyName;
      var backupFunc = new Function(func.tok, func.Name, func.HasStaticKeyword,
          func.IsGhost, func.TypeArgs, func.Formals,
          func.Result, func.ResultType, func.Req,
          func.Reads, func.Ens, func.Decreases,
          func.Body, func.ByMethodTok, func.ByMethodBody,
          func.Attributes, func.SignatureEllipsis);

      using (var wr = new System.IO.StringWriter()) {
        var pr = new Printer(wr, DafnyOptions.PrintModes.DllEmbed);
        pr.UniqueStringBeforeUnderscore = UnderscoreStr;
        func.Body = Expression.CreateBoolLiteral(func.Body.tok, false);
        pr.PrintProgram(program, true);
        var code = $"// {func.FullDafnyName} set to false\n" + Printer.ToStringWithoutNewline(wr) + "\n\n";
        File.WriteAllTextAsync($"/tmp/holeFinder_{funcName}.dfy", code);
      }
      func.Body = backupFunc.Body;
      string dafnyBinaryPath = System.Reflection.Assembly.GetEntryAssembly().Location;
      dafnyBinaryPath = dafnyBinaryPath.Substring(0, dafnyBinaryPath.Length - 4);
      string env = CommandLineOptions.Clo.Environment.Remove(0, 22);
      var argList = env.Split(' ');
      string args = "";
      foreach (var arg in argList) {
        if (!arg.EndsWith(".dfy") && !arg.StartsWith("/hole") && arg.StartsWith("/")) {
          args += arg + " ";
        }
      }
      holeFinderExecutor.createProcessWithOutput(dafnyBinaryPath,
          $"{args} /tmp/holeFinder_{funcName}.dfy /exitAfterFirstError",
          func, $"holeFinder_{funcName}");
    }
    public Function FindHole(Program program, string funcName) {
      UnderscoreStr = RandomString(8);
      holeFinderExecutor.sw = Stopwatch.StartNew();
      Function func = HoleEvaluator.GetFunction(program, funcName);
      if (func == null) {
        Console.WriteLine($"couldn't find function {funcName}. List of all functions:");
        foreach (var kvp in program.ModuleSigs) {
          foreach (var topLevelDecl in ModuleDefinition.AllFunctions(kvp.Value.ModuleDef.TopLevelDecls)) {
            Console.WriteLine(topLevelDecl.FullDafnyName);
          }
        }
        return null;
      }
      foreach (var kvp in program.ModuleSigs) {
        foreach (var topLevelDecl in ModuleDefinition.AllFunctions(kvp.Value.ModuleDef.TopLevelDecls)) {
          Console.WriteLine(topLevelDecl.FullDafnyName);
          if (topLevelDecl.Body != null) {
            PrintWithFuncFalse(program, topLevelDecl);
          }
        }
      }
      holeFinderExecutor.startAndWaitUntilAllProcessesFinishAndDumpTheirOutputs();
      // PrintCallGraphWithBugs(CG);
      return null;
    }
  }
}