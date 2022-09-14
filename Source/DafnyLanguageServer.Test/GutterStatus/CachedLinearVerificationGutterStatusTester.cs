﻿using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Diagnostics;

[TestClass]
public class CachedLinearVerificationGutterStatusTester : LinearVerificationGutterStatusTester {
  private const int MaxTestExecutionTimeMs = 10000;



  // To add a new test, just call VerifyTrace on a given program,
  // the test will fail and give the correct output that can be use for the test
  // Add '//Next<n>:' to edit a line multiple times

  [TestMethod, Timeout(MaxTestExecutionTimeMs)]
  public async Task EnsureCachingDoesNotMakeSquigglyLinesToRemain() {
    await SetUp(new Dictionary<string, string>() {
      { $"{VerifierOptions.Section}:{nameof(VerifierOptions.VerifySnapshots)}", "1" },
      { $"{VerifierOptions.Section}:{nameof(VerifierOptions.VcsCores)}", "1" },
    });
    await VerifyTrace(@"
 .  S  S  |  I  | :method test() {
 .  S  |  |  I  | :  assert true;
 .  S  S  |  I  | :  //Next: 
 .  S  S  |  I  | :}");
  }

  [TestMethod, Timeout(MaxTestExecutionTimeMs)]
  public async Task EnsureCachingDoesNotHideErrors() {
    await SetUp(new Dictionary<string, string>() {
      { $"{VerifierOptions.Section}:{nameof(VerifierOptions.VerifySnapshots)}", "1" },
      { $"{VerifierOptions.Section}:{nameof(VerifierOptions.VcsCores)}", "1" },
    });
    await VerifyTrace(@"
 .  S [S][ ][I][I][ ]:method test() {
 .  S [O][O][o][O][O]:  assert true;
 .  S [=][=][-][=][=]:  assert false;
 .  S [S][ ][I][I][ ]:  //Next: 
 .  S [S][ ][I][I][ ]:}");
  }
}