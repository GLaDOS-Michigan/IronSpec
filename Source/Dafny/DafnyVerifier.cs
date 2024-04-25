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
using Google.Protobuf;

namespace Microsoft.Dafny {

  public class DafnyVerifierClient {
    private const int MaxDepth = 100;
    private int ConcurrentConsumerCount;

    private List<Channel> channelsList = new List<Channel>();
    private int sentRequests;
    private List<string> ServerIpPortList = new List<string>();
    public List<DafnyVerifierService.DafnyVerifierServiceClient> serversList =
      new List<DafnyVerifierService.DafnyVerifierServiceClient>();
    public List<TmpFolder> baseFoldersPath = new List<TmpFolder>();
    private List<List<TmpFolder>> temporaryFoldersList = new List<List<TmpFolder>>();
    private List<AsyncUnaryCall<Empty>> outstandingCleanupTasks = new List<AsyncUnaryCall<Empty>>();
    private List<Queue<IMessage>> tasksQueuePerDepth = new List<Queue<IMessage>>();
    // private ConcurrentQueue<CloneAndVerifyRequest> workerThreadTaskQueue = new ConcurrentQueue<CloneAndVerifyRequest>();
    private BufferBlock<IMessage> tasksBuffer = new BufferBlock<IMessage>();
    private List<Task<int>> consumerTasks = new List<Task<int>>();
    private List<int> taskFinishedPerConsumer = new List<int>();
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
          CreateDir createDir = new CreateDir();
          createDir.Owner = "username";
          baseFoldersPath[index] = serversList[index].CreateTmpFolder(createDir);
        }
      );
      for (int i = 0; i < serversList.Count; i++) {
        temporaryFoldersList[i].Add(baseFoldersPath[i]);
      }
      for (int i = 0; i < MaxDepth; i++) {
        tasksQueuePerDepth.Add(new Queue<IMessage>());
      }
      
      // assuming each server has 40 cores. making double of that consumers
      ConcurrentConsumerCount = serversList.Count * 2 * 40;
      // setting up consumers
      for (int i = 0; i < ConcurrentConsumerCount; i++) {
        consumerTasks.Add(ProcessRequestAsync(tasksBuffer));
      }
    }
    public Stopwatch sw;
    public Dictionary<IMessage, VerificationResponse> dafnyOutput = new Dictionary<IMessage, VerificationResponse>();
    public Dictionary<int, List<IMessage>> requestsList = new Dictionary<int, List<IMessage>>();
    public Dictionary<IMessage, Expression> requestToExpr = new Dictionary<IMessage, Expression>();
    public Dictionary<IMessage, List<ProofEvaluator.ExprStmtUnion>> requestToStmtExprList = new Dictionary<IMessage, List<ProofEvaluator.ExprStmtUnion>>();
    public Dictionary<IMessage, List<Expression>> requestToExprList = new Dictionary<IMessage, List<Expression>>();
    public ConcurrentDictionary<IMessage, AsyncUnaryCall<VerificationResponse>> requestToCall =
      new ConcurrentDictionary<IMessage, AsyncUnaryCall<VerificationResponse>>();
    public Dictionary<IMessage, int> requestToCnt = new Dictionary<IMessage, int>();
    public Dictionary<IMessage, int> requestToAvailableExprAIndex = new Dictionary<IMessage, int>();
    public Dictionary<IMessage, int> requestToAvailableExprBIndex = new Dictionary<IMessage, int>();
    public Dictionary<IMessage, int> requestToPostConditionPosition = new Dictionary<IMessage, int>();
    public Dictionary<IMessage, int> requestToLemmaStartPosition = new Dictionary<IMessage, int>();

    public int tasksProcessed = 0; 
    public void InitializeBaseFoldersInRemoteServers(Program program, string commonPrefix) {
      Parallel.For(0, serversList.Count, new ParallelOptions { MaxDegreeOfParallelism = -1 },
        index => {
          var ipPort = ServerIpPortList[index];
          var ip = ipPort.Split(':')[0];

        string arguments = $"-az --rsh=\" ssh -o StrictHostKeyChecking=no\" --include '*/' --include '*\\.dfy' --exclude '*' {commonPrefix}/ username@{ip}:{baseFoldersPath[index].Path}/";
        ProcessStartInfo startInfo = new ProcessStartInfo() { FileName = "/usr/bin/rsync", Arguments = arguments, };
        Process proc = new Process() { StartInfo = startInfo, };
        proc.Start();
        proc.WaitForExit();
        if (proc.ExitCode != 0) {
          Console.WriteLine($"Unsuccessful rsync for node{index}: Confirm connection between nodes");
          System.Environment.Exit(-1);
        }
        }
      );
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

    public void CheckIfCorrectAnswer(IMessage request, VerificationResponse response) {
      var output = response.Response;
      if (request is CloneAndVerifyRequest) {
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
      }
      else if (request is VerificationRequest) {
        // In this case, all verification requests should be considered to determine
        // the correntness of an expression. So, we do nothing here.
      }
    }

    public async Task<int> ProcessRequestAsync(IReceivableSourceBlock<IMessage> source) {
      tasksProcessed = 0;
      while (await source.OutputAvailableAsync()) {
        if (source.TryReceive(out IMessage request)) {
          start:
          try {
            if (!requestToCall.ContainsKey(request)) {
              RestartTask(request);
            }
            Console.WriteLine($"calling await for #{requestToCnt[request]}");
            VerificationResponse response = await requestToCall[request];
            Console.WriteLine($"finished await for #{requestToCnt[request]}");
            var output = response.Response;
            CheckIfCorrectAnswer(request, response);
            dafnyOutput[request] = response;
            if (DafnyOptions.O.HoleEvaluatorDumpOutput) {
              await File.WriteAllTextAsync($"{DafnyOptions.O.EvaluatorWorkingDirectory}{requestToCnt[request]}_0.txt",
                request.ToString());
              await File.WriteAllTextAsync($"{DafnyOptions.O.EvaluatorWorkingDirectory}{OutputPrefix}_{requestToCnt[request]}_0.txt",
                (requestToExpr.ContainsKey(request) ? "// " + Printer.ExprToString(requestToExpr[request]) + "\n" : "") +
                (requestToCnt.ContainsKey(request) ? "// " + requestToCnt[request] + "\n" : "") + output + "\n");
            }
            // Console.WriteLine($"finish executing {requestToCnt[request]}");
          } catch (RpcException ex) {
            Console.WriteLine($"{sw.ElapsedMilliseconds / 1000}:: Restarting task #{requestToCnt[request]} {ex.Message}");
            RestartTask(request);
            goto start;
          }
          tasksProcessed++;
        }
      }
      return tasksProcessed;
    }

    public async Task<bool> startProofTasksAccordingToPriority() {
       var startSize = 0;
      for (int i = 0; i < MaxDepth; i++) {
        // Console.WriteLine($"depth size = {tasksQueuePerDepth[i].Count}");
        foreach (var request in tasksQueuePerDepth[i]) {
          tasksBuffer.Post(request);
          startSize++;
        }
      }         
        //  var startSize = tasksBuffer.Count;
          // Console.WriteLine("SIZE B = " +startSize);

      while (!doneWithTasks(startSize))
      {
          // Console.WriteLine("Still waiitng");
          await Task.Delay(25);
      }
      tasksBuffer.Complete();

      // waiting on consumers
      for (int i = 0; i < ConcurrentConsumerCount; i++) {
        taskFinishedPerConsumer.Add(await consumerTasks[i]);
      }
      // for (int i = 0; i < ConcurrentConsumerCount; i++) {
      //   Console.WriteLine($"Consumer #{i} finished {taskFinishedPerConsumer[i]} tasks");
      // }


      return true;
    }

private bool doneWithTasks(int taskSize)
{
  try
  {
    // Console.WriteLine("starting = " + taskSize + " :: done = " + tasksProcessed);
    
    return taskSize == tasksProcessed;
  }catch{
    return false;
  }
  // return true;
}


public void clearTasks()
{
      tasksQueuePerDepth = new List<Queue<IMessage>>();
          for (int i = 0; i < MaxDepth; i++) {
      tasksQueuePerDepth.Add(new Queue<IMessage>());
    }

    tasksBuffer = new BufferBlock<IMessage>();
    for (int i = 0; i < ConcurrentConsumerCount; i++) {
      consumerTasks.Add(ProcessRequestAsync(tasksBuffer));
    }
    // return true;
}


    private void RestartTask(IMessage request) {
      // var prevTask = requestToCall[request];
      var serverId = requestToCnt[request] % serversList.Count;
        Console.WriteLine("Restart  == at Server (" + serverId + ") for #"+requestToCnt[request]);
        // Console.WriteLine($"calling await for #{requestToCnt[request]}");

      if (request is CloneAndVerifyRequest) {
        AsyncUnaryCall<VerificationResponse> task = serversList[serverId].CloneAndVerifyAsync(
          request as CloneAndVerifyRequest,
          deadline: DateTime.UtcNow.AddMinutes(30000));
        requestToCall[request] = task;
      }
      else if (request is VerificationRequest) {
        // Console.WriteLine($"sending request {(request as VerificationRequest).Path}");
        AsyncUnaryCall<VerificationResponse> task = serversList[serverId].VerifyAsync(
          request as VerificationRequest,
          deadline: DateTime.UtcNow.AddMinutes(1000));
        requestToCall[request] = task;
      }
      else {
        throw new NotSupportedException($"invalid request type : {request.ToString()}");
      }
    }

    public List<List<TmpFolder>> getTempFilePath()
    {
      return temporaryFoldersList;
    }
    
    public Boolean WriteToRemoteFile(string code, int cnt, string remoteFilePath)
    {
      var serverId = cnt % serversList.Count;
      VerificationRequest request = new VerificationRequest();
      request.Code = code;
      request.Path = remoteFilePath;
      Empty response = serversList[serverId].WriteToRemoteFile(request);
      return true;
    }
    public void runDafny(string code, List<string> args, ExpressionFinder.ExpressionDepth exprDepth,
        int cnt, int postConditionPos, int lemmaStartPos, string remoteFilePath) {
      sentRequests++;
      // if (sentRequests == 500) {
      //   sentRequests = 0;
      //   ResetChannel();
      // }
      VerificationRequest request = new VerificationRequest();
      request.Code = code;
      request.Path = remoteFilePath;
      foreach (var arg in args) {
        request.Arguments.Add(arg);
      }
      if (!requestsList.ContainsKey(cnt)) {
        requestsList.Add(cnt, new List<IMessage>());
      }
      requestsList[cnt].Add(request);
      tasksQueuePerDepth[1].Enqueue(request);
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
      Console.WriteLine("sending to server: " + serverId);
      AsyncUnaryCall<VerificationResponse> task = serversList[serverId].CloneAndVerifyAsync(request);
      requestToCall[request] = task;
      if (!requestsList.ContainsKey(requestsList.Count)) {
        requestsList.Add(requestsList.Count, new List<IMessage>());
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
        requestsList.Add(cnt, new List<IMessage>());
      }
      requestsList[cnt].Add(request);
      requestToStmtExprList[request] = exprStmtList;
      requestToCnt[request] = cnt;
      dafnyOutput[request] = new VerificationResponse();
      if (cnt < consumerTasks.Count || (tasksBuffer.Count < consumerTasks.Count / 4)) {
        tasksBuffer.Post(request);
      }
      else {
        int maxDepth = 0;
        foreach (var stmtExpr in exprStmtList) {
          maxDepth = Math.Max(maxDepth, stmtExpr.Depth);
        }
        tasksQueuePerDepth[maxDepth].Enqueue(request);
      }
    }

    public void runDafnyProofCheck(string code, List<string> args, List<ProofEvaluator.ExprStmtUnion> exprStmtList,
        int cnt, string filePath, string lemmaName) {
      sentRequests++;
      // if (sentRequests == 500) {
      //   sentRequests = 0;
      //   ResetChannel();
      // }
      CloneAndVerifyRequest request = new CloneAndVerifyRequest();
      request.Code = code;
      var serverId = cnt % serversList.Count;
      request.DirectoryPath = baseFoldersPath[serverId].Path;
      request.ModifyingFile = filePath;
      foreach (var arg in args) {
        request.Arguments.Add(arg);
      }
      request.Arguments.Add($"/proc:*{lemmaName}*");
      if (!requestsList.ContainsKey(cnt)) {
        requestsList.Add(cnt, new List<IMessage>());
      }
      requestsList[cnt].Add(request);
      requestToStmtExprList[request] = exprStmtList;
      requestToCnt[request] = cnt;
      dafnyOutput[request] = new VerificationResponse();
      // if (cnt < consumerTasks.Count || (tasksBuffer.Count < consumerTasks.Count / 4)) {
      // tasksBuffer.Post(request);
      // }
      // else {
      int maxDepth = 0;
      foreach (var stmtExpr in exprStmtList) {
        maxDepth = Math.Max(maxDepth, stmtExpr.Depth);
      }
      tasksQueuePerDepth[maxDepth].Enqueue(request);
      // }
    }
  }
}