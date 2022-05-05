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

  public class HoleFinderExecutor {
    public Stopwatch sw;
    public Dictionary<Process, string> dafnyOutput = new Dictionary<Process, string>();
    public Dictionary<Process, string> inputFileName = new Dictionary<Process, string>();
    public List<Process> dafnyProcesses = new List<Process>();
    private List<Process> readyProcesses = new List<Process>();
    public Dictionary<Process, int> processToPostConditionPosition = new Dictionary<Process, int>();
    public Dictionary<Process, Function> processToFunc = new Dictionary<Process, Function>();
    public Dictionary<Function, Process> funcToProcess = new Dictionary<Function, Process>();

    public void startAndWaitUntilAllProcessesFinishAndDumpTheirOutputs() {
      // ResizeDafnyOutputList(readyProcesses.Count);
      Parallel.For(0, readyProcesses.Count,
        new ParallelOptions { MaxDegreeOfParallelism = Environment.ProcessorCount / 2 },
        i => {
          readyProcesses[i].Start();
          readyProcesses[i].WaitForExit();
          var firstOutput = readyProcesses[i].StandardOutput.ReadToEnd();
          var p = readyProcesses[i];
          // Console.WriteLine($"2 {i}");
          p.Close();
          var output = firstOutput;
          var expectedOutput =
            $"/tmp/{inputFileName[p]}.dfy({processToPostConditionPosition[p]},0): Error: A postcondition might not hold on this return path.";
          var expectedInconclusiveOutputStart =
            $"/tmp/{inputFileName[p]}.dfy({processToPostConditionPosition[p]},{HoleEvaluator.validityLemmaNameStartCol}): Verification inconclusive";
          if (DafnyExecutor.IsCorrectOutput(output, expectedOutput, expectedInconclusiveOutputStart)) {
            if (processToFunc[p].Name == "nullFunc") {
              Console.WriteLine($"{sw.ElapsedMilliseconds / 1000}:: proof goes through, and there is no hole");
            } else {
              Console.WriteLine($"{sw.ElapsedMilliseconds / 1000}:: possible bug in {processToFunc[p]}");
            }
          }
          dafnyOutput[p] = output;
          var args = p.StartInfo.Arguments;
          File.WriteAllTextAsync($"/tmp/output_{inputFileName[p]}.txt",
            "// " + args + "\n" + output + "\n");
        });
      readyProcesses.Clear();
    }

    public void createProcessWithOutput(string command, string args, Function func,
        int postConditionPos, string inputFile) {
      Process p = new Process();
      p.StartInfo = new ProcessStartInfo(command, args);
      p.StartInfo.RedirectStandardOutput = true;
      p.StartInfo.RedirectStandardError = false;
      p.StartInfo.UseShellExecute = false;
      p.StartInfo.CreateNoWindow = true;
      readyProcesses.Add(p);
      dafnyProcesses.Add(p);
      processToPostConditionPosition[p] = postConditionPos;
      processToFunc[p] = func;
      funcToProcess[func] = p;
      dafnyOutput[p] = "";
      inputFileName[p] = inputFile;
    }
  }
}