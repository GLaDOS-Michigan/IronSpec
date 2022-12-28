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

    private List<Channel> channelsList = new List<Channel>();
    private int sentRequests;
    private List<string> ServerIpPortList = new List<string>();
    private List<DafnyVerifierService.DafnyVerifierServiceClient> serversList =
      new List<DafnyVerifierService.DafnyVerifierServiceClient>();
    private List<TmpFolder> baseFoldersPath = new List<TmpFolder>();
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
      }
      Parallel.For(0, serversList.Count,
        index => {
          Empty emptyProto = new Empty();
          baseFoldersPath[index] = serversList[index].CreateTmpFolder(emptyProto);
        }
      );
    }
    public Stopwatch sw;
    public Dictionary<VerificationRequest, VerificationResponse> dafnyOutput = new Dictionary<VerificationRequest, VerificationResponse>();
    public Dictionary<int, List<VerificationRequest>> requestsList = new Dictionary<int, List<VerificationRequest>>();
    public Dictionary<VerificationRequest, Expression> requestToExpr = new Dictionary<VerificationRequest, Expression>();
    public Dictionary<VerificationRequest, List<Expression>> requestToExprList = new Dictionary<VerificationRequest, List<Expression>>();
    public Dictionary<VerificationRequest, AsyncUnaryCall<VerificationResponse>> requestToCall =
      new Dictionary<VerificationRequest, AsyncUnaryCall<VerificationResponse>>();
    public Dictionary<VerificationRequest, int> requestToCnt = new Dictionary<VerificationRequest, int>();
    public Dictionary<VerificationRequest, int> requestToAvailableExprAIndex = new Dictionary<VerificationRequest, int>();
    public Dictionary<VerificationRequest, int> requestToAvailableExprBIndex = new Dictionary<VerificationRequest, int>();
    public Dictionary<VerificationRequest, int> requestToPostConditionPosition = new Dictionary<VerificationRequest, int>();
    public Dictionary<VerificationRequest, int> requestToLemmaStartPosition = new Dictionary<VerificationRequest, int>();

    public void InitializeBaseFoldersInRemoteServers(Program program, string commonPrefix) {
      for (int i = 0; i < serversList.Count; i++) {
        var ipPort = ServerIpPortList[i];
        var ip = ipPort.Split(':')[0];

        string arguments = $"-az --rsh=\" ssh -o StrictHostKeyChecking=no\" --include '*/' --include '*\\.dfy' --exclude '*' {commonPrefix}/ arminvak@{ip}:{baseFoldersPath[i].Path}/";
        ProcessStartInfo startInfo = new ProcessStartInfo() { FileName = "/usr/bin/rsync", Arguments = arguments, }; 
        Process proc = new Process() { StartInfo = startInfo, };
        proc.Start();
        proc.WaitForExit();
      }
      // var filesList = new List<string>();
      // foreach (var file in program.DefaultModuleDef.Includes) {
      //   filesList.Add(file.CanonicalPath);
      // }

    }

    public TmpFolder DuplicateAllFiles(int cnt, string changingFilePath) {
      var serverId = cnt % serversList.Count;
      TmpFolder duplicateFileRequest = new TmpFolder();
      duplicateFileRequest.Path = baseFoldersPath[serverId].Path;
      duplicateFileRequest.ModifyingFile = changingFilePath;
      TmpFolder targetFolder = serversList[serverId].DuplicateFolder(duplicateFileRequest);
      return targetFolder;
    }

    public static Result IsCorrectOutputForValidityCheck(string output, string expectedOutput, string expectedInconclusiveOutputStart) {
      if (output.EndsWith("1 error\n")) {
        var outputList = output.Split('\n');
        for(int i = 1; i <= 7; i++) {
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

    public static Result IsCorrectOutputForNoErrors(string output)
    {
      if (output.EndsWith("0 errors\n")) {
        return Result.CorrectProof;
      }
      else {
        return Result.IncorrectProof;
      }
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
              foreach (var expr in requestToExprList[request]) {
                str += ($"{sep}{Printer.ExprToString(expr)}");
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

    private void RestartTask(VerificationRequest request) {
      var prevTask = requestToCall[request];
      var serverId = requestToCnt[request] % serversList.Count;
      AsyncUnaryCall<VerificationResponse> task = serversList[serverId].VerifyAsync(request,
        deadline: DateTime.UtcNow.AddMinutes(30000));
      requestToCall[request] = task;
    }
    public void runDafny(string code, List<string> args, Expression expr,
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
        requestsList.Add(cnt, new List<VerificationRequest>());
      }
      requestsList[cnt].Add(request);
      var serverId = cnt % serversList.Count;
      AsyncUnaryCall<VerificationResponse> task = serversList[serverId].VerifyAsync(request,
        deadline: DateTime.UtcNow.AddMinutes(30000));
      requestToCall[request] = task;
      requestToExpr[request] = expr;
      requestToCnt[request] = cnt;
      requestToPostConditionPosition[request] = postConditionPos;
      requestToLemmaStartPosition[request] = lemmaStartPos;
      dafnyOutput[request] = new VerificationResponse();
    }

    public void runDafny(string code, string args,
        int availableExprAIndex, int availableExprBIndex,
        int lemmaStartPos, int postConditionPos) {
      VerificationRequest request = new VerificationRequest();
      request.Code = code;
      request.Arguments.Add(args);
      var serverId = (availableExprAIndex * availableExprBIndex) % serversList.Count;
      AsyncUnaryCall<VerificationResponse> task = serversList[serverId].VerifyAsync(request);
      requestToCall[request] = task;
      if (!requestsList.ContainsKey(requestsList.Count)) {
        requestsList.Add(requestsList.Count, new List<VerificationRequest>());
      }
      requestsList[requestsList.Count].Add(request);
      requestToAvailableExprAIndex[request] = availableExprAIndex;
      requestToAvailableExprBIndex[request] = availableExprBIndex;
      requestToPostConditionPosition[request] = postConditionPos;
      requestToLemmaStartPosition[request] = lemmaStartPos;
      dafnyOutput[request] = new VerificationResponse();
    }

    public void runDafnyProofCheck(string code, List<string> args, List<Expression> exprList, int cnt) {
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
      if (!requestsList.ContainsKey(cnt)) {
        requestsList.Add(cnt, new List<VerificationRequest>());
      }
      requestsList[cnt].Add(request);
      var serverId = cnt % serversList.Count;
      AsyncUnaryCall<VerificationResponse> task = serversList[serverId].VerifyAsync(request,
        deadline: DateTime.UtcNow.AddMinutes(30000));
      requestToCall[request] = task;
      requestToExprList[request] = exprList;
      requestToCnt[request] = cnt;
      dafnyOutput[request] = new VerificationResponse();
    }
  }
}