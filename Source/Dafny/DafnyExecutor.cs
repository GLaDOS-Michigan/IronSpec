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
    public Dictionary<Process, int> processToPostConditionPosition = new Dictionary<Process, int>();
    public Dictionary<Process, int> processToLemmaStartPosition = new Dictionary<Process, int>();

    public static Result IsCorrectOutput(string output, string expectedOutput, string expectedInconclusiveOutputStart) {
      if (output.EndsWith("1 error\n")) {
        var outputList = output.Split('\n');
        return ((outputList.Length >= 7) && (outputList[outputList.Length - 7] == expectedOutput)) ? Result.CorrectProof : Result.IncorrectProof;
      } else if (output.EndsWith("1 inconclusive\n")) {
        var outputList = output.Split('\n');
        return ((outputList.Length >= 4) && outputList[outputList.Length - 4].StartsWith(expectedInconclusiveOutputStart)) ? Result.CorrectProofByTimeout : Result.IncorrectProof;
      } else {
        return Result.IncorrectProof;
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

    public void startAndWaitUntilAllProcessesFinishAndDumpTheirOutputs(bool runOnlyOnce) {
      // ResizeDafnyOutputList(readyProcesses.Count);
      Parallel.For(0, readyProcesses.Count,
        new ParallelOptions { MaxDegreeOfParallelism = Environment.ProcessorCount / 2 },
        i => {
          // if (i % 1000 == 0) {
          //   Console.WriteLine($"Executing {i}");
          // }
          readyProcesses[i].Start();
          readyProcesses[i].WaitForExit();
          var firstOutput = readyProcesses[i].StandardOutput.ReadToEnd();
          if (!runOnlyOnce && (!firstOutput.EndsWith("0 errors\n")) &&
              (!firstOutput.EndsWith($"resolution/type errors detected in {inputFileName[readyProcesses[i]]}.dfy\n"))) {
            var p = readyProcesses[i];
            // Console.WriteLine($"1 {i}");
            p.Close();

            File.WriteAllTextAsync($"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}/output_{inputFileName[p]}_0.txt",
              (processToExpr.ContainsKey(p) ? "// " + Printer.ExprToString(processToExpr[p]) + "\n" : "") +
              "// " + p.StartInfo.Arguments + "\n" + firstOutput + "\n");

            var args = p.StartInfo.Arguments.Split(' ');
            args = args.SkipLast(1).Append("/exitAfterFirstError").ToArray();
            // args = args.Append("/exitAfterFirstError");
            p.StartInfo = new ProcessStartInfo(p.StartInfo.FileName, String.Join(' ', args));
            p.StartInfo.RedirectStandardOutput = true;
            p.StartInfo.RedirectStandardError = false;
            p.StartInfo.UseShellExecute = false;
            p.StartInfo.CreateNoWindow = true;

            p.Start();
            p.WaitForExit();
            var output = p.StandardOutput.ReadToEnd();
            var expectedOutput =
              $"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}{inputFileName[p]}.dfy({processToPostConditionPosition[p]},0): Error: A postcondition might not hold on this return path.";
            var expectedInconclusiveOutputStart =
              $"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}{inputFileName[p]}.dfy({processToLemmaStartPosition[p]},{MutationEvaluator.validityLemmaNameStartCol}): Verification inconclusive";
            var result = IsCorrectOutput(output, expectedOutput, expectedInconclusiveOutputStart);
            if (result != Result.IncorrectProof) {
              Console.WriteLine($"{sw.ElapsedMilliseconds / 1000}:: correct answer {result.ToString()} #{processToCnt[p]}: {Printer.ExprToString(processToExpr[p])}");
            }
            dafnyOutput[readyProcesses[i]] = output;
            File.WriteAllTextAsync($"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}output_{inputFileName[readyProcesses[i]]}_1.txt",
              (processToExpr.ContainsKey(readyProcesses[i]) ? "// " + Printer.ExprToString(processToExpr[readyProcesses[i]]) + "\n" : "") +
              "// " + String.Join(' ', args) + "\n" + output + "\n");
          } else {
            var p = readyProcesses[i];
            // Console.WriteLine($"2 {i}");
            p.Close();
            var output = firstOutput;
            var expectedOutput =
              $"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}{inputFileName[p]}.dfy({processToPostConditionPosition[p]},0): Error: A postcondition might not hold on this return path.";
            var expectedInconclusiveOutputStart =
              $"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}{inputFileName[p]}.dfy({processToLemmaStartPosition[p]},{MutationEvaluator.validityLemmaNameStartCol}): Verification inconclusive";
            var result = IsCorrectOutput(output, expectedOutput, expectedInconclusiveOutputStart);
            if (result != Result.IncorrectProof) {
              Console.WriteLine($"{sw.ElapsedMilliseconds / 1000}:: correct answer {result.ToString()} #{processToCnt[p]}: {Printer.ExprToString(processToExpr[p])}");
            }
            dafnyOutput[p] = output;
            var args = p.StartInfo.Arguments;
            File.WriteAllTextAsync($"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}output_{inputFileName[p]}_0.txt",
              (processToExpr.ContainsKey(p) ? "// " + Printer.ExprToString(processToExpr[p]) + "\n" : "") +
              "// " + args + "\n" + output + "\n");
          }
          // Console.WriteLine($"finish executing {i}");
        });
      readyProcesses.Clear();
    }

    public void createProcessWithOutput(string command, string args, Expression expr,
        int cnt, int postConditionPos, int lemmaStartPos, string inputFile) {
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
      processToPostConditionPosition[p] = postConditionPos;
      processToLemmaStartPosition[p] = lemmaStartPos;
      dafnyOutput[p] = "";
      inputFileName[p] = inputFile;
    }

    public void createProcessWithOutput(string command, string args,
        int availableExprAIndex, int availableExprBIndex, 
        int lemmaStartPos, int postConditionPos, string inputFile) {
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
      processToPostConditionPosition[p] = postConditionPos;
      processToLemmaStartPosition[p] = lemmaStartPos;
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