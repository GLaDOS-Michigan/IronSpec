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
using Grpc.Core;

namespace Microsoft.Dafny {

  public class DafnyVerifierClient {

    private Channel channel;
    private DafnyVerifierService.DafnyVerifierServiceClient client;
    DafnyVerifierClient(string serverIpPort) {
      channel = new Channel(serverIpPort, ChannelCredentials.Insecure);
      client = new DafnyVerifierService.DafnyVerifierServiceClient(channel);
    }
    public Stopwatch sw;
    public Dictionary<Task, string> dafnyOutput = new Dictionary<Task, string>();
    public Dictionary<Task, string> inputFileName = new Dictionary<Task, string>();
    public List<Task> dafnyTasks = new List<Task>();
    private List<Task> readyTasks = new List<Task>();
    public Dictionary<Task, Expression> taskToExpr = new Dictionary<Task, Expression>();
    public Dictionary<Task, int> taskToCnt = new Dictionary<Task, int>();
    public Dictionary<Task, int> taskToAvailableExprAIndex = new Dictionary<Task, int>();
    public Dictionary<Task, int> taskToAvailableExprBIndex = new Dictionary<Task, int>();
    public Dictionary<Task, int> taskToPostConditionPosition = new Dictionary<Task, int>();
    public Dictionary<Task, int> taskToLemmaStartPosition = new Dictionary<Task, int>();

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

    public static Task<Task<T>>[] Interleaved<T>(IEnumerable<Task<T>> tasks) {
      var inputTasks = tasks.ToList();

      var buckets = new TaskCompletionSource<Task<T>>[inputTasks.Count];
      var results = new Task<Task<T>>[buckets.Length];
      for (int i = 0; i < buckets.Length; i++) {
        buckets[i] = new TaskCompletionSource<Task<T>>();
        results[i] = buckets[i].Task;
      }

      int nextTaskIndex = -1;
      Action<Task<T>> continuation = completed => {
        var bucket = buckets[Interlocked.Increment(ref nextTaskIndex)];
        bucket.TrySetResult(completed);
      };

      foreach (var inputTask in inputTasks)
        inputTask.ContinueWith(continuation, CancellationToken.None, TaskContinuationOptions.ExecuteSynchronously, TaskScheduler.Default);

      return results;
    }

    public void startAndWaitUntilAllProcessesFinishAndDumpTheirOutputs() {
      foreach (var bucket in Interleaved(readyTasks)) {
        var t = await bucket;
        VerificationResponse response = await t;
        var output = response.response;
        var expectedOutput =
          $"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}{inputFileName[p]}.dfy({processToPostConditionPosition[p]},0): Error: A postcondition might not hold on this return path.";
        var expectedInconclusiveOutputStart =
          $"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}{inputFileName[p]}.dfy({processToLemmaStartPosition[p]},{HoleEvaluator.validityLemmaNameStartCol}): Verification inconclusive";
        var result = IsCorrectOutput(output, expectedOutput, expectedInconclusiveOutputStart);
        if (result != Result.IncorrectProof) {
          Console.WriteLine($"{sw.ElapsedMilliseconds / 1000}:: correct answer {result.ToString()} #{processToCnt[p]}: {Printer.ExprToString(processToExpr[p])}");
        }
        dafnyOutput[p] = output;
        var args = p.StartInfo.Arguments;
        File.WriteAllTextAsync($"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}output_{inputFileName[p]}_0.txt",
          (processToExpr.ContainsKey(p) ? "// " + Printer.ExprToString(processToExpr[p]) + "\n" : "") +
          "// " + args + "\n" + output + "\n");
        // Console.WriteLine($"finish executing {i}");
      }
    }

    public void runDafny(string code, string args, Expression expr,
        int cnt, int postConditionPos, int lemmaStartPos) {
      VerificationRequest request = new VerificationRequest();
      request.Code = code;
      request.Arguments.Add(args);
      Task task = client.VerifyAsync(request);
      readyTasks.Add(task);
      dafnyTasks.Add(task);
      taskToExpr[task] = expr;
      taskToCnt[task] = cnt;
      taskToPostConditionPosition[task] = postConditionPos;
      taskToLemmaStartPosition[task] = lemmaStartPos;
      dafnyOutput[task] = "";
      inputFileName[task] = inputFile;
    }

    public void runDafny(string code, string args,
        int availableExprAIndex, int availableExprBIndex,
        int lemmaStartPos, int postConditionPos) {
      VerificationRequest request = new VerificationRequest();
      request.Code = code;
      request.Arguments.Add(args);
      Task task = client.VerifyAsync(request);
      readyTasks.Add(task);
      dafnyTasks.Add(task);
      taskToAvailableExprAIndex[task] = availableExprAIndex;
      taskToAvailableExprBIndex[task] = availableExprBIndex;
      taskToPostConditionPosition[task] = postConditionPos;
      taskToLemmaStartPosition[task] = lemmaStartPos;
      inputFileName[task] = inputFile;
      dafnyOutput[task] = "";
    }
  }
}