﻿using System.Linq;
using System.Threading.Tasks;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using System.Threading;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various;

[TestClass]
public class PluginsTestWithVerification : PluginsTestBase {
  [TestInitialize]
  public async Task SetUp() {
    await SetUpPlugin();
  }

  protected override string LibraryName =>
    "PluginsTestVerification";

  protected override string[] CommandLineArgument =>
    new[] { $@"--dafny:plugins:0={LibraryPath},""because\\ \""whatever""" };

  [TestMethod]
  public async Task EnsureItIsPossibleToLoadAPluginAndContinueVerification() {
    // This code will run with the plugin from PluginsAdvancedTest, but that plugin won't throw an exception on the code below.
    var documentItem = CreateTestDocument("function test(): nat { -1 }");
    await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var resolutionReport = await DiagnosticReceiver.AwaitNextNotificationAsync(CancellationToken.None);
    Assert.AreEqual(documentItem.Uri, resolutionReport.Uri);
    var verificationReport = await DiagnosticReceiver.AwaitNextNotificationAsync(CancellationToken.None);
    Assert.AreEqual(documentItem.Uri, resolutionReport.Uri);
    var diagnostics = verificationReport.Diagnostics.ToArray();
    Assert.AreEqual(1 + DafnyOptions.DefaultPlugins.Count, DafnyOptions.O.Plugins.Count,
      "Not exactly 1 plugin loaded");
    Assert.AreEqual(2, diagnostics.Length, LibraryPath + " did not raise an error.");
    Assert.AreEqual("Plugin Error that does not prevent verification", diagnostics[0].Message);
    Assert.AreEqual(new Range((0, 9), (0, 13)), diagnostics[0].Range);
    Assert.AreEqual("value does not satisfy the subset constraints of 'nat'", diagnostics[1].Message);
    Assert.AreEqual(new Range((0, 23), (0, 24)), diagnostics[1].Range);
  }

  [TestCleanup]
  public void DoCleanup() {
    CleanupPlugin();
  }
}
