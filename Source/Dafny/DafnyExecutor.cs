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

  public class DafnyExecutor {
    public Dictionary<Process, List<string>> dafnyOutput = new Dictionary<Process, List<string>>();
    public Dictionary<Process, string> inputFileName = new Dictionary<Process, string>();
    public List<Process> dafnyProcesses = new List<Process>();
    public Dictionary<Process, Expression> processToExpr = new Dictionary<Process, Expression>();
    public Dictionary<Process, int> processToCnt = new Dictionary<Process, int>();
    public Dictionary<Process, int> processToCorrExprAIndex = new Dictionary<Process, int>();
    public Dictionary<Process, int> processToCorrExprBIndex = new Dictionary<Process, int>();
    public Dictionary<Process, int> processToLemmaPosition = new Dictionary<Process, int>();

    public void waitUntilAllProcessesFinishAndDumpTheirOutputs() {
      foreach (var p in dafnyProcesses) {
        p.WaitForExit();
      }
      foreach (var p in dafnyProcesses) {
        File.WriteAllTextAsync($"/tmp/output_{inputFileName[p]}.txt",
          String.Join('\n', dafnyOutput[p]) + "\n");
      }
    }

    public void startProcessWithOutput(string command, string args, Expression expr,
        int cnt, int lemmaPos, string inputFile) {
      Process p = new Process();
      p.StartInfo = new ProcessStartInfo(command, args);
      p.StartInfo.RedirectStandardOutput = true;
      p.StartInfo.RedirectStandardError = false;
      p.StartInfo.UseShellExecute = false;
      p.StartInfo.CreateNoWindow = true;
      p.OutputDataReceived += new DataReceivedEventHandler(DafnyOutputHandler);
      p.Start();
      p.BeginOutputReadLine();
      dafnyProcesses.Add(p);
      processToExpr[p] = expr;
      processToCnt[p] = cnt;
      processToLemmaPosition[p] = lemmaPos;
      dafnyOutput[p] = new List<string>();
      inputFileName[p] = inputFile;
    }

    public void startProcessWithOutput(string command, string args,
        int corrExprAIndex, int corrExprBIndex, int lemmaPos, string inputFile) {
      Process p = new Process();
      p.StartInfo = new ProcessStartInfo(command, args);
      p.StartInfo.RedirectStandardOutput = true;
      p.StartInfo.RedirectStandardError = false;
      p.StartInfo.UseShellExecute = false;
      p.StartInfo.CreateNoWindow = true;
      p.OutputDataReceived += new DataReceivedEventHandler(DafnyOutputHandler);
      p.Start();
      p.BeginOutputReadLine();
      dafnyProcesses.Add(p);
      processToCorrExprAIndex[p] = corrExprAIndex;
      processToCorrExprBIndex[p] = corrExprBIndex;
      processToLemmaPosition[p] = lemmaPos;
      inputFileName[p] = inputFile;
      dafnyOutput[p] = new List<string>();
    }

    private void DafnyOutputHandler(object sendingProcess,
            DataReceivedEventArgs outLine) {
      // Collect the net view command output.
      if (!String.IsNullOrEmpty(outLine.Data)) {
        // Add the text to the collected output.
        dafnyOutput[sendingProcess as Process].Add(outLine.Data);
      }
    }

  }
}