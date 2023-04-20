//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------
using System;
using System.Text;
using System.IO;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Diagnostics;
using System.Reflection;
using System.Linq;
using System.Threading.Tasks;

namespace Microsoft.Dafny {
  public class IncludeParser {
    private Program program;
    private Dictionary<string, List<string>> affectedFilesList = new Dictionary<string, List<string>>();
    public string commonPrefix;
    private int commonPrefixLength;

    public IncludeParser(Program program) {
      this.program = program;
      CreateIncludeGraph();
    }
    public string NormalizedTo(string baseName, string path)
    {
      var samplesLocal = new List<string>();
      baseName = baseName.Remove(baseName.LastIndexOf("/"));
      var localPath = path.Remove(path.LastIndexOf("/"));
      samplesLocal.Add(baseName);
      samplesLocal.Add(localPath);
      var localCommonPrefix = new string(
        samplesLocal.First().Substring(0, samplesLocal.Min(s => s.Length))
        .TakeWhile((c, i) => samplesLocal.All(s => s[i] == c)).ToArray());
      // commonPrefixLength = commonPrefix.Length;
      var updatedPath = path.Remove(0, localCommonPrefix.Length+1);
      return updatedPath;
    }

    public string Normalized(string path)
    {
      path = path.Remove(0, commonPrefixLength);
      var directoryList = path.Split('/').ToList();
      for (int i = 0; i < directoryList.Count; i++) {
        if (directoryList[i] == "..") {
          directoryList.RemoveAt(i - 1);
          directoryList.RemoveAt(i - 1);
          i -= 2;
        }
      //  if (directoryList[i] == "..") {
      //     for(int j = 0; j < i; j++){
      //       directoryList.RemoveAt(0);
      //     }
      //     break;
      //  }
      }
      return String.Join('/', directoryList);
    }

    private void CreateIncludeGraph()
    {
      var samples = new List<string>();
      if (program.DefaultModuleDef.Includes.Count == 0) {
        // commonPrefix = Path.GetDirectoryName(program.FullName);
        commonPrefix = Path.GetDirectoryName(program.FullName) + "/";
        commonPrefixLength = commonPrefix.Length;
        return;
      }else{
            samples.Add(program.FullName);
      }
      if(DafnyOptions.O.ProofLocation != null)
      {
        Console.WriteLine(DafnyOptions.O.ProofLocation);
        samples.Add(DafnyOptions.O.ProofLocation);
      }

      foreach (var file in program.DefaultModuleDef.Includes) {
        samples.Add(file.CanonicalPath);
      }
      commonPrefix = new string(
        samples.First().Substring(0, samples.Min(s => s.Length))
        .TakeWhile((c, i) => samples.All(s => s[i] == c)).ToArray());
      commonPrefixLength = commonPrefix.Length;
      foreach (var includePair in program.DefaultModuleDef.Includes) {
        var includedFilename = Normalized(includePair.IncludedFilename);
        var includerFilename = Normalized(includePair.IncluderFilename);
        if (!affectedFilesList.ContainsKey(includedFilename)) {
          affectedFilesList.Add(includedFilename, new List<string>());
        }
        affectedFilesList[includedFilename].Add(includerFilename);
      }
    }

    public IEnumerable<string> GetListOfAffectedFilesBy(string file) {
      if (!affectedFilesList.ContainsKey(file)) {
        yield break;
      }
      foreach (var affected in affectedFilesList[file]) {
        yield return affected;
        foreach (var x in GetListOfAffectedFilesBy(affected)) {
          yield return x;
        }
      }
    }
  }
}