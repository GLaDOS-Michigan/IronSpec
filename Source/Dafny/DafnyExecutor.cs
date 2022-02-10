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
using System.Threading.Tasks;

namespace Microsoft.Dafny {

  public class DafnyExecutor {
    public Dictionary<Process, List<string>> dafnyOutput = new Dictionary<Process, List<string>>();
    public Dictionary<Process, string> inputFileName = new Dictionary<Process, string>();
    public List<Process> dafnyProcesses = new List<Process>();
    private List<Process> readyProcesses = new List<Process>();
    public Dictionary<Process, Expression> processToExpr = new Dictionary<Process, Expression>();
    public Dictionary<Process, int> processToCnt = new Dictionary<Process, int>();
    public Dictionary<Process, int> processToAvailableExprAIndex = new Dictionary<Process, int>();
    public Dictionary<Process, int> processToAvailableExprBIndex = new Dictionary<Process, int>();
    public Dictionary<Process, int> processToLemmaPosition = new Dictionary<Process, int>();

    public void startAndWaitUntilAllProcessesFinishAndDumpTheirOutputs() {
      Parallel.For(0, readyProcesses.Count,
        new ParallelOptions { MaxDegreeOfParallelism = Environment.ProcessorCount - 1 },
        i => {
          if (i % 1000 == 0) {
            Console.WriteLine($"Executing {i}");
          }
          readyProcesses[i].Start();
          readyProcesses[i].BeginOutputReadLine();
          readyProcesses[i].WaitForExit();
          File.WriteAllTextAsync($"/tmp/output_{inputFileName[readyProcesses[i]]}.txt",
            String.Join('\n', dafnyOutput[readyProcesses[i]]) + "\n");
        });
      readyProcesses.Clear();
    }

    public void createProcessWithOutput(string command, string args, Expression expr,
        int cnt, int lemmaPos, string inputFile) {
      Process p = new Process();
      p.StartInfo = new ProcessStartInfo(command, args);
      p.StartInfo.RedirectStandardOutput = true;
      p.StartInfo.RedirectStandardError = false;
      p.StartInfo.UseShellExecute = false;
      p.StartInfo.CreateNoWindow = true;
      p.OutputDataReceived += new DataReceivedEventHandler(DafnyOutputHandler);
      // p.Start();
      // p.BeginOutputReadLine();
      readyProcesses.Add(p);
      dafnyProcesses.Add(p);
      processToExpr[p] = expr;
      processToCnt[p] = cnt;
      processToLemmaPosition[p] = lemmaPos;
      dafnyOutput[p] = new List<string>();
      inputFileName[p] = inputFile;
    }

    public void createProcessWithOutput(string command, string args,
        int availableExprAIndex, int availableExprBIndex, int lemmaPos, string inputFile) {
      Process p = new Process();
      p.StartInfo = new ProcessStartInfo(command, args);
      p.StartInfo.RedirectStandardOutput = true;
      p.StartInfo.RedirectStandardError = false;
      p.StartInfo.UseShellExecute = false;
      p.StartInfo.CreateNoWindow = true;
      p.OutputDataReceived += new DataReceivedEventHandler(DafnyOutputHandler);
      // p.Start();
      // p.BeginOutputReadLine();
      readyProcesses.Add(p);
      dafnyProcesses.Add(p);
      processToAvailableExprAIndex[p] = availableExprAIndex;
      processToAvailableExprBIndex[p] = availableExprBIndex;
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