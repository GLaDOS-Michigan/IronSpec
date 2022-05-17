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
using System.Threading;
using System.Threading.Tasks;
using Grpc.Core;

namespace Microsoft.Dafny {

  public class DafnyVerifierClient {

    private Channel channel;
    private DafnyVerifierService.DafnyVerifierServiceClient client;
    private string OutputPrefix;
    public DafnyVerifierClient(string serverIpPort, string outputPrefix) {
      channel = new Channel(serverIpPort, ChannelCredentials.Insecure);
      client = new DafnyVerifierService.DafnyVerifierServiceClient(channel);
      OutputPrefix = outputPrefix;
    }
    public Stopwatch sw;
    public Dictionary<AsyncUnaryCall<VerificationResponse>, VerificationResponse> dafnyOutput = new Dictionary<AsyncUnaryCall<VerificationResponse>, VerificationResponse>();
    public List<AsyncUnaryCall<VerificationResponse>> dafnyTasks = new List<AsyncUnaryCall<VerificationResponse>>();
    private List<AsyncUnaryCall<VerificationResponse>> readyTasks = new List<AsyncUnaryCall<VerificationResponse>>();
    public Dictionary<AsyncUnaryCall<VerificationResponse>, Expression> taskToExpr = new Dictionary<AsyncUnaryCall<VerificationResponse>, Expression>();
    public Dictionary<AsyncUnaryCall<VerificationResponse>, int> taskToCnt = new Dictionary<AsyncUnaryCall<VerificationResponse>, int>();
    public Dictionary<AsyncUnaryCall<VerificationResponse>, int> taskToAvailableExprAIndex = new Dictionary<AsyncUnaryCall<VerificationResponse>, int>();
    public Dictionary<AsyncUnaryCall<VerificationResponse>, int> taskToAvailableExprBIndex = new Dictionary<AsyncUnaryCall<VerificationResponse>, int>();
    public Dictionary<AsyncUnaryCall<VerificationResponse>, int> taskToPostConditionPosition = new Dictionary<AsyncUnaryCall<VerificationResponse>, int>();
    public Dictionary<AsyncUnaryCall<VerificationResponse>, int> taskToLemmaStartPosition = new Dictionary<AsyncUnaryCall<VerificationResponse>, int>();

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

    // public static Task<Task<T>>[] Interleaved<T>(IEnumerable<Task<T>> tasks) {
    //   var inputTasks = tasks.ToList();

    //   var buckets = new TaskCompletionSource<Task<T>>[inputTasks.Count];
    //   var results = new Task<Task<T>>[buckets.Length];
    //   for (int i = 0; i < buckets.Length; i++) {
    //     buckets[i] = new TaskCompletionSource<Task<T>>();
    //     results[i] = buckets[i].Task;
    //   }

    //   int nextTaskIndex = -1;
    //   Action<Task<T>> continuation = completed => {
    //     var bucket = buckets[Interlocked.Increment(ref nextTaskIndex)];
    //     bucket.TrySetResult(completed);
    //   };

    //   foreach (var inputTask in inputTasks)
    //     inputTask.ContinueWith(continuation, CancellationToken.None, TaskContinuationOptions.ExecuteSynchronously, TaskScheduler.Default);

    //   return results;
    // }

    public async Task<bool> startAndWaitUntilAllProcessesFinishAndDumpTheirOutputs() {
      foreach (var call in readyTasks) {
        VerificationResponse response = await call;
        var output = response.Response;
        var expectedOutput =
          $"{response.FileName}({taskToPostConditionPosition[call]},0): Error: A postcondition might not hold on this return path.";
        var expectedInconclusiveOutputStart =
          $"{response.FileName}({taskToLemmaStartPosition[call]},{HoleEvaluator.validityLemmaNameStartCol}): Verification inconclusive";
        var result = IsCorrectOutput(output, expectedOutput, expectedInconclusiveOutputStart);
        if (result != Result.IncorrectProof) {
          Console.WriteLine($"{sw.ElapsedMilliseconds / 1000}:: correct answer {result.ToString()} #{taskToCnt[call]}: {Printer.ExprToString(taskToExpr[call])}");
        }
        dafnyOutput[call] = response;
        File.WriteAllTextAsync($"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}{OutputPrefix}_{taskToCnt[call]}_0.txt",
          (taskToExpr.ContainsKey(call) ? "// " + Printer.ExprToString(taskToExpr[call]) + "\n" : "") + output + "\n");
        // Console.WriteLine($"finish executing {i}");
      }
      return true;
    }

    public void runDafny(string code, List<string> args, Expression expr,
        int cnt, int postConditionPos, int lemmaStartPos) {
      VerificationRequest request = new VerificationRequest();
      request.Code = code;
      foreach (var arg in args) {
        request.Arguments.Add(arg);
      }
      AsyncUnaryCall<VerificationResponse> task = client.VerifyAsync(request);
      readyTasks.Add(task);
      dafnyTasks.Add(task);
      taskToExpr[task] = expr;
      taskToCnt[task] = cnt;
      taskToPostConditionPosition[task] = postConditionPos;
      taskToLemmaStartPosition[task] = lemmaStartPos;
      dafnyOutput[task] = new VerificationResponse();
    }

    public void runDafny(string code, string args,
        int availableExprAIndex, int availableExprBIndex,
        int lemmaStartPos, int postConditionPos) {
      VerificationRequest request = new VerificationRequest();
      request.Code = code;
      request.Arguments.Add(args);
      AsyncUnaryCall<VerificationResponse> task = client.VerifyAsync(request);
      readyTasks.Add(task);
      dafnyTasks.Add(task);
      taskToAvailableExprAIndex[task] = availableExprAIndex;
      taskToAvailableExprBIndex[task] = availableExprBIndex;
      taskToPostConditionPosition[task] = postConditionPos;
      taskToLemmaStartPosition[task] = lemmaStartPos;
      dafnyOutput[task] = new VerificationResponse();
    }
  }
}