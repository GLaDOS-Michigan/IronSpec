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
    private int sentRequests;
    private string ServerIpPort;
    private DafnyVerifierService.DafnyVerifierServiceClient client;
    private string OutputPrefix;
    private Random rand = new Random();
    public DafnyVerifierClient(string serverIpPort, string outputPrefix) {
      // var defaultMethodConfig = new MethodConfig {
      //   Names = { MethodName.Default },
      //   RetryPolicy = new RetryPolicy {
      //     MaxAttempts = 5,
      //     InitialBackoff = TimeSpan.FromMinutes(20),
      //     MaxBackoff = TimeSpan.FromMinutes(20),
      //     BackoffMultiplier = 1.5,
      //     RetryableStatusCodes = { StatusCode.DeadlineExceeded }
      //   }
      // };
      // var defaultMethodConfig = new MethodConfig {
      //   Names = { MethodName.Default },
      //   RetryPolicy = new RetryPolicy {
      //     MaxAttempts = 3,
      //     InitialBackoff = TimeSpan.FromMinutes(20),
      //     MaxBackoff = TimeSpan.FromMinutes(20),
      //     BackoffMultiplier = 1.5,
      //     RetryableStatusCodes =
      //     {
      //       // Whatever status codes you want to look for
      //       StatusCode.Unavailable, StatusCode.DeadlineExceeded
      //     }
      //   }
      // };
      this.ServerIpPort = serverIpPort;
      ResetChannel();
      sentRequests = 0;
      OutputPrefix = outputPrefix;
    }

    private void ResetChannel() {
      List<ChannelOption> options = new List<ChannelOption>();
      options.Add(new ChannelOption("grpc.enable_retries", 1));
      double r = 1 + rand.NextDouble() / 2;
      r = Math.Round(r, 3, MidpointRounding.ToEven);
      var channelOption = "{\"retryPolicy\": { \"maxAttempts\": 4, \"initialBackoff\": \"1200000s\", " +
        "\"maxBackoff\": \"1200000s\", \"backoffMultiplier\": " + r.ToString() + ", \"retryableStatusCodes\": " +
        "[\"UNAVAILABLE\", \"DEADLINE_EXCEEDED\"]} }";
      Console.WriteLine("Creating channel with option:");
      Console.WriteLine(channelOption);
      options.Add(new ChannelOption("grpc.service_config", channelOption));
      channel = new Channel(ServerIpPort, ChannelCredentials.Insecure, options);
      client = new DafnyVerifierService.DafnyVerifierServiceClient(channel);
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
      for (int i = 0; i < readyTasks.Count; i++) {
        var call = readyTasks[i];
        try {
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
        } catch (RpcException ex) {
          Console.WriteLine($"{sw.ElapsedMilliseconds / 1000}:: {taskToCnt[call]} {ex.Message}");
          // restart(i);
          dafnyOutput[call] = new VerificationResponse();
          dafnyOutput[call].Response = ex.Message;
          dafnyOutput[call].FileName = "exception";
          File.WriteAllTextAsync($"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}{OutputPrefix}_{taskToCnt[call]}_0.txt",
            (taskToExpr.ContainsKey(call) ? "// " + Printer.ExprToString(taskToExpr[call]) + "\n" : "") + ex.Message + "\n");
        }
      }
      return true;
    }

    public void runDafny(string code, List<string> args, Expression expr,
        int cnt, int postConditionPos, int lemmaStartPos) {
      sentRequests++;
      // if (sentRequests == 500) {
      //   sentRequests = 0;
      //   ResetChannel();
      // }
      VerificationRequest request = new VerificationRequest();
      request.Code = code;
      foreach (var arg in args) {
        request.Arguments.Add(arg);
      }
      AsyncUnaryCall<VerificationResponse> task = client.VerifyAsync(request,
        deadline: DateTime.UtcNow.AddMinutes(20000));
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