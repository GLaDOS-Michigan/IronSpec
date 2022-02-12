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
    public Stopwatch sw;
    public Dictionary<Process, string> dafnyOutput = new Dictionary<Process, string>();
    public Dictionary<Process, string> inputFileName = new Dictionary<Process, string>();
    public List<Process> dafnyProcesses = new List<Process>();
    private List<Process> readyProcesses = new List<Process>();
    public Dictionary<Process, Expression> processToExpr = new Dictionary<Process, Expression>();
    public Dictionary<Process, int> processToCnt = new Dictionary<Process, int>();
    public Dictionary<Process, int> processToAvailableExprAIndex = new Dictionary<Process, int>();
    public Dictionary<Process, int> processToAvailableExprBIndex = new Dictionary<Process, int>();
    public Dictionary<Process, int> processToLemmaPosition = new Dictionary<Process, int>();

    public static bool IsCorrectOutput(string output, string expectedOutput) {
      if (output.EndsWith("1 error\n")) {
        var outputList = output.Split('\n');
        return ((outputList.Length >= 7) && (outputList[outputList.Length - 7] == expectedOutput));
      } else {
        return false;
      }
    }

    // private void ResizeDafnyOutputList(int size) {
    //   int count = dafnyOutput.Count;
    //   if (size < count) {
    //     return;
    //   }
    //   if (size > dafnyOutput.Capacity)   // Optimization
    //     dafnyOutput.Capacity = size;

    //   dafnyOutput.AddRange(Enumerable.Repeat("", size - count));
    // }

    public void startAndWaitUntilAllProcessesFinishAndDumpTheirOutputs(bool isMainExecution) {
      // ResizeDafnyOutputList(readyProcesses.Count);
      Parallel.For(0, readyProcesses.Count,
        new ParallelOptions { MaxDegreeOfParallelism = Environment.ProcessorCount - 1 },
        i => {
          if (i % 1000 == 0) {
            Console.WriteLine($"Executing {i}");
          }
          readyProcesses[i].Start();
          // readyProcesses[i].BeginOutputReadLine();
          readyProcesses[i].WaitForExit();
          var firstOutput = readyProcesses[i].StandardOutput.ReadToEnd();
          // dafnyOutput[i] = firstOutput;
          if (isMainExecution && (!firstOutput.EndsWith("0 errors\n")) &&
              (!firstOutput.EndsWith($"resolution/type errors detected in {inputFileName[readyProcesses[i]]}.dfy\n"))) {
            readyProcesses[i].Close();
            var args = readyProcesses[i].StartInfo.Arguments.Split(' ');
            args = args.SkipLast(1).ToArray();
            var p = readyProcesses[i];
            p.StartInfo = new ProcessStartInfo(readyProcesses[i].StartInfo.FileName, String.Join(' ', args));
            p.StartInfo.RedirectStandardOutput = true;
            p.StartInfo.RedirectStandardError = false;
            p.StartInfo.UseShellExecute = false;
            p.StartInfo.CreateNoWindow = true;
            // p.OutputDataReceived += new DataReceivedEventHandler(DafnyOutputHandler);
            // processToExpr[p] = processToExpr[readyProcesses[i]];
            // processToCnt[p] = processToCnt[readyProcesses[i]];
            // processToLemmaPosition[p] = processToLemmaPosition[readyProcesses[i]];
            // inputFileName[p] = inputFileName[readyProcesses[i]];
            // dafnyOutput[p] = new List<string>();

            // remove previous process
            // processToExpr.Remove(readyProcesses[i]);
            // processToCnt.Remove(readyProcesses[i]);
            // processToLemmaPosition.Remove(readyProcesses[i]);
            // inputFileName.Remove(readyProcesses[i]);
            // dafnyOutput.Remove(readyProcesses[i]);

            // readyProcesses[i] = p;
            // dafnyProcesses[i] = p;
            p.Start();
            // p.BeginOutputReadLine();
            p.WaitForExit();
            var output = p.StandardOutput.ReadToEnd();
            // dafnyOutput[i] = output;
            var expectedOutput =
              $"/tmp/{inputFileName[p]}.dfy({processToLemmaPosition[p] + 3},0): Error: A postcondition might not hold on this return path.";
            // Console.WriteLine($"finish {i} => {dafnyProcesses[i].StartInfo.Arguments} -- {output}\n{expectedOutput}");
            if (IsCorrectOutput(output, expectedOutput)) {
              Console.WriteLine($"{sw.ElapsedMilliseconds / 1000}:: correct answer #{i}: {Printer.ExprToString(processToExpr[p])}");
            }
            dafnyOutput[readyProcesses[i]] = output;
            File.WriteAllTextAsync($"/tmp/output_{inputFileName[readyProcesses[i]]}.txt",
              output + "\n");
            // Console.WriteLine($"new output {String.Join(" - ", dafnyOutput[readyProcesses[i]])}");
          } else {
            // Debug.Assert(inputFileName.ContainsKey(readyProcesses[i]), $"{i}");
            // Debug.Assert(dafnyOutput.ContainsKey(readyProcesses[i]), $"{i}");
            dafnyOutput[readyProcesses[i]] = firstOutput;
            File.WriteAllTextAsync($"/tmp/output_{inputFileName[readyProcesses[i]]}.txt",
              firstOutput + "\n");
          }
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
      // p.OutputDataReceived += new DataReceivedEventHandler(DafnyOutputHandler);
      // p.Start();
      // p.BeginOutputReadLine();
      readyProcesses.Add(p);
      dafnyProcesses.Add(p);
      processToExpr[p] = expr;
      processToCnt[p] = cnt;
      processToLemmaPosition[p] = lemmaPos;
      dafnyOutput[p] = "";
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
      // p.OutputDataReceived += new DataReceivedEventHandler(DafnyOutputHandler);
      // p.Start();
      // p.BeginOutputReadLine();
      readyProcesses.Add(p);
      dafnyProcesses.Add(p);
      processToAvailableExprAIndex[p] = availableExprAIndex;
      processToAvailableExprBIndex[p] = availableExprBIndex;
      processToLemmaPosition[p] = lemmaPos;
      inputFileName[p] = inputFile;
      dafnyOutput[p] = "";
    }

    // private void DafnyOutputHandler(object sendingProcess,
    //         DataReceivedEventArgs outLine) {
    //   // Collect the net view command output.
    //   if (!String.IsNullOrEmpty(outLine.Data)) {
    //     // Add the text to the collected output.
    //     if (!dafnyOutput.ContainsKey(sendingProcess as Process)) {
    //       Console.WriteLine($"process does not exist {(sendingProcess as Process).StartInfo.Arguments}");
    //     } else {
    //       dafnyOutput[sendingProcess as Process].Add(outLine.Data);
    //     }
    //   }
    // }

  }
}