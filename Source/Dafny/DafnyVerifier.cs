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
using System.Collections.Concurrent;
using System.Diagnostics.Contracts;
using System.Diagnostics;
using System.Reflection;
using System.Linq;
using Microsoft.Boogie;
using System.Threading;
using System.Threading.Tasks;
using System.Threading.Tasks.Dataflow;
using Grpc.Core;

namespace Microsoft.Dafny {

  public class DafnyVerifierClient {
    private const int MaxDepth = 100;

    private List<Channel> channelsList = new List<Channel>();
    private int sentRequests;
    private List<string> ServerIpPortList = new List<string>();
    private List<DafnyVerifierService.DafnyVerifierServiceClient> serversList =
      new List<DafnyVerifierService.DafnyVerifierServiceClient>();
    private List<TmpFolder> baseFoldersPath = new List<TmpFolder>();
    private List<List<TmpFolder>> temporaryFoldersList = new List<List<TmpFolder>>();
    private List<AsyncUnaryCall<Empty>> outstandingCleanupTasks = new List<AsyncUnaryCall<Empty>>();
    private List<Queue<CloneAndVerifyRequest>> tasksQueuePerDepth = new List<Queue<CloneAndVerifyRequest>>();
    private ConcurrentQueue<CloneAndVerifyRequest> workerThreadTaskQueue = new ConcurrentQueue<CloneAndVerifyRequest>();
    private string OutputPrefix;
    private Random rand = new Random();
    public DafnyVerifierClient(string serverIpPortFileName, string outputPrefix) {
      sentRequests = 0;
      OutputPrefix = outputPrefix;

      foreach (string line in System.IO.File.ReadLines(serverIpPortFileName)) {
        ServerIpPortList.Add(line);
        channelsList.Add(new Channel(line, ChannelCredentials.Insecure));
        serversList.Add(new DafnyVerifierService.DafnyVerifierServiceClient(
          channelsList[channelsList.Count - 1]));
        baseFoldersPath.Add(new TmpFolder());
        temporaryFoldersList.Add(new List<TmpFolder>());
      }
      Parallel.For(0, serversList.Count,
        index => {
          Empty emptyProto = new Empty();
          baseFoldersPath[index] = serversList[index].CreateTmpFolder(emptyProto);
        }
      );
      for (int i = 0; i < serversList.Count; i++) {
        temporaryFoldersList[i].Add(baseFoldersPath[i]);
      }
      for (int i = 0; i < MaxDepth; i++) {
        tasksQueuePerDepth.Add(new Queue<CloneAndVerifyRequest>());
      }
    }
    public Stopwatch sw;
    public Dictionary<CloneAndVerifyRequest, VerificationResponse> dafnyOutput = new Dictionary<CloneAndVerifyRequest, VerificationResponse>();
    public Dictionary<int, List<CloneAndVerifyRequest>> requestsList = new Dictionary<int, List<CloneAndVerifyRequest>>();
    public Dictionary<CloneAndVerifyRequest, Expression> requestToExpr = new Dictionary<CloneAndVerifyRequest, Expression>();
    public Dictionary<CloneAndVerifyRequest, List<ProofEvaluator.ExprStmtUnion>> requestToStmtExprList = new Dictionary<CloneAndVerifyRequest, List<ProofEvaluator.ExprStmtUnion>>();
    public Dictionary<CloneAndVerifyRequest, List<Expression>> requestToExprList = new Dictionary<CloneAndVerifyRequest, List<Expression>>();
    public ConcurrentDictionary<CloneAndVerifyRequest, AsyncUnaryCall<VerificationResponse>> requestToCall =
      new ConcurrentDictionary<CloneAndVerifyRequest, AsyncUnaryCall<VerificationResponse>>();
    public Dictionary<CloneAndVerifyRequest, int> requestToCnt = new Dictionary<CloneAndVerifyRequest, int>();
    public Dictionary<CloneAndVerifyRequest, int> requestToAvailableExprAIndex = new Dictionary<CloneAndVerifyRequest, int>();
    public Dictionary<CloneAndVerifyRequest, int> requestToAvailableExprBIndex = new Dictionary<CloneAndVerifyRequest, int>();
    public Dictionary<CloneAndVerifyRequest, int> requestToPostConditionPosition = new Dictionary<CloneAndVerifyRequest, int>();
    public Dictionary<CloneAndVerifyRequest, int> requestToLemmaStartPosition = new Dictionary<CloneAndVerifyRequest, int>();

    public void InitializeBaseFoldersInRemoteServers(Program program, string commonPrefix) {
      for (int i = 0; i < serversList.Count; i++) {
        var ipPort = ServerIpPortList[i];
        var ip = ipPort.Split(':')[0];

        string arguments = $"-az --rsh=\" ssh -o StrictHostKeyChecking=no\" --include '*/' --include '*\\.dfy' --exclude '*' {commonPrefix}/ edgoldwe@{ip}:{baseFoldersPath[i].Path}/";
        ProcessStartInfo startInfo = new ProcessStartInfo() { FileName = "/usr/bin/rsync", Arguments = arguments, };
        Process proc = new Process() { StartInfo = startInfo, };
        proc.Start();
        proc.WaitForExit();
        if (proc.ExitCode != 0) {
          Console.WriteLine($"Unsuccessful rsync for node{i}: Confirm connection between nodes");
          System.Environment.Exit(-1);
        }
      }
      // var filesList = new List<string>();
      // foreach (var file in program.DefaultModuleDef.Includes) {
      //   filesList.Add(file.CanonicalPath);
      // }

    }


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
    
    public TmpFolder DuplicateAllFiles(int cnt, string changingFilePath) {
      var serverId = cnt % serversList.Count;
      TmpFolder duplicateFileRequest = new TmpFolder();
      duplicateFileRequest.Path = baseFoldersPath[serverId].Path;
      duplicateFileRequest.ModifyingFile = changingFilePath;
      TmpFolder targetFolder = serversList[serverId].DuplicateFolder(duplicateFileRequest);
      temporaryFoldersList[serverId].Add(targetFolder);
      return targetFolder;
    }

    public static Result IsCorrectOutputForValidityCheck(string output, string expectedOutput, string expectedInconclusiveOutputStart) {
      if (output.EndsWith("1 error\n")) {
        var outputList = output.Split('\n');
        for (int i = 1; i <= 7; i++) {
          if ((outputList.Length >= i) && (outputList[outputList.Length - i] == expectedOutput)) {
            return Result.CorrectProof;
          }
        }
        return Result.IncorrectProof;
      } else if (output.EndsWith("1 inconclusive\n")) {
        var outputList = output.Split('\n');
        return ((outputList.Length >= 4) && outputList[outputList.Length - 4].StartsWith(expectedInconclusiveOutputStart)) ? Result.CorrectProofByTimeout : Result.IncorrectProof;
      } else {
        return Result.IncorrectProof;
      }
    }

    public static Result IsCorrectOutputForNoErrors(string output) {
      if (output.EndsWith("0 errors\n")) {
        return Result.CorrectProof;
      } else {
        return Result.IncorrectProof;
      }
    }

    public void Cleanup() {
      for (int serverId = 0; serverId < temporaryFoldersList.Count; serverId++) {
        for (int i = 0; i < temporaryFoldersList[serverId].Count; i++) {
          AsyncUnaryCall<Empty> task = serversList[serverId].RemoveFolderAsync(
            temporaryFoldersList[serverId][i],
            deadline: DateTime.UtcNow.AddMinutes(30));
          outstandingCleanupTasks.Add(task);
        }
      }
      temporaryFoldersList.Clear();
    }

    public async Task<bool> FinalizeCleanup() {
      for (int i = 0; i < outstandingCleanupTasks.Count; i++) {
        Empty response = await outstandingCleanupTasks[i];
      }
      return true;
    }

    public async Task<bool> startAndWaitUntilAllProcessesFinishAndDumpTheirOutputs() {
      await Parallel.ForEachAsync(requestsList.Values.SelectMany(x => x).ToList(),
        async (request, tmp) => {
        start:
          try {
            VerificationResponse response = await requestToCall[request];
            dafnyOutput[request] = response;
          } catch (RpcException ex) {
            Console.WriteLine($"{sw.ElapsedMilliseconds / 1000}:: Restarting task #{requestToCnt[request]} {ex.Message}");
            RestartTask(request);
            goto start;
          }
        });
      return true;
    }
    public async Task<bool> startProofTasksAndWaitUntilAllProcessesFinishAndDumpTheirOutputs() {
      await Parallel.ForEachAsync(requestsList.Values.SelectMany(x => x).ToList(),
        async (request, tmp) => {
        start:
          try {
            VerificationResponse response = await requestToCall[request];
            var output = response.Response;
            if (output.EndsWith("0 errors\n")) {
              var str = $"{sw.ElapsedMilliseconds / 1000}:: correct answer #{requestToCnt[request]}: ";
              var sep = "";
              foreach (var stmtExpr in requestToStmtExprList[request]) {
                if (stmtExpr.Expr != null) {
                  str += ($"{sep}{Printer.ExprToString(stmtExpr.Expr)}");
                } else {
                  str += ($"{sep}{Printer.StatementToString(stmtExpr.Stmt)}");
                }
                sep = ", ";
              }
              Console.WriteLine(str);
            }
            dafnyOutput[request] = response;
            await File.WriteAllTextAsync($"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}{OutputPrefix}_{requestToCnt[request]}_0.txt",
              (requestToExpr.ContainsKey(request) ? "// " + Printer.ExprToString(requestToExpr[request]) + "\n" : "") +
              (requestToCnt.ContainsKey(request) ? "// " + requestToCnt[request] + "\n" : "") + output + "\n");
            // Console.WriteLine($"finish executing {requestToCnt[request]}");
          } catch (RpcException ex) {
            Console.WriteLine($"{sw.ElapsedMilliseconds / 1000}:: Restarting task #{requestToCnt[request]} {ex.Message}");
            RestartTask(request);
            goto start;
          }
        });
      return true;
    }

    // public async Task<int> ProcessRequestAsync(IReceivableSourceBlock<CloneAndVerifyRequest> source) {
    //   int tasksProcessed = 0;
    //   while (await source.OutputAvailableAsync()) {
    //     while (source.TryReceive(out CloneAndVerifyRequest request)) {
    //       start:
    //       try {
    //         if (!requestToCall.ContainsKey(request)) {
    //           RestartTask(request);
    //         }
    //         // Console.WriteLine($"{i}: calling await for #{requestToCnt[request]}");
    //         VerificationResponse response = await requestToCall[request];
    //         // Console.WriteLine($"{i}: finished await for #{requestToCnt[request]}");
    //         var output = response.Response;
    //         if (output.EndsWith("0 errors\n")) {
    //           var str = $"{sw.ElapsedMilliseconds / 1000}:: correct answer #{requestToCnt[request]}: ";
    //           var sep = "";
    //           foreach (var stmtExpr in requestToStmtExprList[request]) {
    //             if (stmtExpr.Expr != null) {
    //               str += ($"{sep}{Printer.ExprToString(stmtExpr.Expr)}");
    //             } else {
    //               str += ($"{sep}{Printer.StatementToString(stmtExpr.Stmt)}");
    //             }
    //             sep = ", ";
    //           }
    //           Console.WriteLine(str);
    //         }
    //         dafnyOutput[request] = response;
    //         await File.WriteAllTextAsync($"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}{OutputPrefix}_{requestToCnt[request]}_0.txt",
    //           (requestToExpr.ContainsKey(request) ? "// " + Printer.ExprToString(requestToExpr[request]) + "\n" : "") +
    //           (requestToCnt.ContainsKey(request) ? "// " + requestToCnt[request] + "\n" : "") + output + "\n");
    //         // Console.WriteLine($"finish executing {requestToCnt[request]}");
    //       } catch (RpcException ex) {
    //         Console.WriteLine($"{sw.ElapsedMilliseconds / 1000}:: Restarting task #{requestToCnt[request]} {ex.Message}");
    //         RestartTask(request);
    //         goto start;
    //       }
    //       tasksProcessed++;
    //     }
    //   }
    //   return tasksProcessed;
    // }

    public async Task<bool> startProofTasksAccordingToPriority() {
      for (int i = 0; i < MaxDepth; i++) {
        Console.WriteLine($"depth size = {tasksQueuePerDepth[i].Count}");
        var options = new ParallelOptions {MaxDegreeOfParallelism = int.MaxValue};
        await Parallel.ForEachAsync(tasksQueuePerDepth[i], options,
          async (request, tmp) => {
          start:
            try {
              if (!requestToCall.ContainsKey(request)) {
                RestartTask(request);
              }
              // Console.WriteLine($"{i}: calling await for #{requestToCnt[request]}");
              VerificationResponse response = await requestToCall[request];
              // Console.WriteLine($"{i}: finished await for #{requestToCnt[request]}");
              var output = response.Response;
              if (output.EndsWith("0 errors\n")) {
                var str = $"{sw.ElapsedMilliseconds / 1000}:: correct answer #{requestToCnt[request]}: ";
                var sep = "";
                foreach (var stmtExpr in requestToStmtExprList[request]) {
                  if (stmtExpr.Expr != null) {
                    str += ($"{sep}{Printer.ExprToString(stmtExpr.Expr)}");
                  } else {
                    str += ($"{sep}{Printer.StatementToString(stmtExpr.Stmt)}");
                  }
                  sep = ", ";
                }
                Console.WriteLine(str);
              }
              dafnyOutput[request] = response;
              await File.WriteAllTextAsync($"{DafnyOptions.O.HoleEvaluatorWorkingDirectory}{OutputPrefix}_{requestToCnt[request]}_0.txt",
                (requestToExpr.ContainsKey(request) ? "// " + Printer.ExprToString(requestToExpr[request]) + "\n" : "") +
                (requestToCnt.ContainsKey(request) ? "// " + requestToCnt[request] + "\n" : "") + output + "\n");
            // Console.WriteLine($"finish executing {requestToCnt[request]}");
          } catch (RpcException ex) {
              Console.WriteLine($"{sw.ElapsedMilliseconds / 1000}:: Restarting task #{requestToCnt[request]} {ex.Message}");
              RestartTask(request);
              goto start;
            }
          });
      }
      return true;
    }


    private void RestartTask(CloneAndVerifyRequest request) {
      // var prevTask = requestToCall[request];
      var serverId = requestToCnt[request] % serversList.Count;
      AsyncUnaryCall<VerificationResponse> task = serversList[serverId].CloneAndVerifyAsync(request,
        deadline: DateTime.UtcNow.AddMinutes(30000));
      requestToCall[request] = task;
    }
    public void runDafny(string code, List<string> args, ExpressionFinder.ExpressionDepth exprDepth,
        int cnt, int postConditionPos, int lemmaStartPos, string remoteFilePath) {
      sentRequests++;
      // if (sentRequests == 500) {
      //   sentRequests = 0;
      //   ResetChannel();
      // }
      CloneAndVerifyRequest request = new CloneAndVerifyRequest();
      request.Code = code;
      request.ModifyingFile = remoteFilePath;
      foreach (var arg in args) {
        request.Arguments.Add(arg);
      }
      if (!requestsList.ContainsKey(cnt)) {
        requestsList.Add(cnt, new List<CloneAndVerifyRequest>());
      }
      requestsList[cnt].Add(request);
      tasksQueuePerDepth[exprDepth.depth].Enqueue(request);
      // var serverId = cnt % serversList.Count;
      // AsyncUnaryCall<VerificationResponse> task = serversList[serverId].VerifyAsync(request,
      //   deadline: DateTime.UtcNow.AddMinutes(30));
      // requestToCall[request] = task;
      requestToExpr[request] = exprDepth.expr;
      requestToCnt[request] = cnt;
      requestToPostConditionPosition[request] = postConditionPos;
      requestToLemmaStartPosition[request] = lemmaStartPos;
      dafnyOutput[request] = new VerificationResponse();
    }

    public void runDafny(string code, string args,
        int availableExprAIndex, int availableExprBIndex,
        int lemmaStartPos, int postConditionPos) {
      throw new NotImplementedException("Check compatibility with tasksQueuePerDepth");
      CloneAndVerifyRequest request = new CloneAndVerifyRequest();
      request.Code = code;
      request.Arguments.Add(args);
      var serverId = (availableExprAIndex * availableExprBIndex) % serversList.Count;
      AsyncUnaryCall<VerificationResponse> task = serversList[serverId].CloneAndVerifyAsync(request);
      requestToCall[request] = task;
      if (!requestsList.ContainsKey(requestsList.Count)) {
        requestsList.Add(requestsList.Count, new List<CloneAndVerifyRequest>());
      }
      requestsList[requestsList.Count].Add(request);
      requestToAvailableExprAIndex[request] = availableExprAIndex;
      requestToAvailableExprBIndex[request] = availableExprBIndex;
      requestToPostConditionPosition[request] = postConditionPos;
      requestToLemmaStartPosition[request] = lemmaStartPos;
      dafnyOutput[request] = new VerificationResponse();
    }

    public void runDafnyProofCheck(string code, List<string> args, List<ProofEvaluator.ExprStmtUnion> exprStmtList, int cnt) {
      sentRequests++;
      // if (sentRequests == 500) {
      //   sentRequests = 0;
      //   ResetChannel();
      // }
      CloneAndVerifyRequest request = new CloneAndVerifyRequest();
      request.Code = code;
      foreach (var arg in args) {
        request.Arguments.Add(arg);
      }
      if (!requestsList.ContainsKey(cnt)) {
        requestsList.Add(cnt, new List<CloneAndVerifyRequest>());
      }
      requestsList[cnt].Add(request);
      int maxDepth = 0;
      foreach (var stmtExpr in exprStmtList) {
        maxDepth = Math.Max(maxDepth, stmtExpr.Depth);
      }
      tasksQueuePerDepth[maxDepth].Enqueue(request);
      // var serverId = cnt % serversList.Count;
      // AsyncUnaryCall<VerificationResponse> task = serversList[serverId].VerifyAsync(request,
      //   deadline: DateTime.UtcNow.AddMinutes(30));
      // requestToCall[request] = task;
      requestToStmtExprList[request] = exprStmtList;
      requestToCnt[request] = cnt;
      dafnyOutput[request] = new VerificationResponse();
    }

    public void runDafnyProofCheck(string code, List<string> args, List<ProofEvaluator.ExprStmtUnion> exprStmtList,
        int cnt, string remoteFilePath, string lemmaName) {
      sentRequests++;
      // if (sentRequests == 500) {
      //   sentRequests = 0;
      //   ResetChannel();
      // }
      CloneAndVerifyRequest request = new CloneAndVerifyRequest();
      request.Code = code;
      var serverId = cnt % serversList.Count;
      request.DirectoryPath = baseFoldersPath[serverId].Path;
      request.ModifyingFile = remoteFilePath;
      foreach (var arg in args) {
        request.Arguments.Add(arg);
      }
      request.Arguments.Add($"/proc:*{lemmaName}*");
      if (!requestsList.ContainsKey(cnt)) {
        requestsList.Add(cnt, new List<CloneAndVerifyRequest>());
      }
      requestsList[cnt].Add(request);
      int maxDepth = 0;
      foreach (var stmtExpr in exprStmtList) {
        maxDepth = Math.Max(maxDepth, stmtExpr.Depth);
      }
      tasksQueuePerDepth[maxDepth].Enqueue(request);
      // AsyncUnaryCall<VerificationResponse> task = serversList[serverId].VerifyAsync(request,
      //   deadline: DateTime.UtcNow.AddMinutes(30));
      // requestToCall[request] = task;
      requestToStmtExprList[request] = exprStmtList;
      requestToCnt[request] = cnt;
      dafnyOutput[request] = new VerificationResponse();
    }
  }
}