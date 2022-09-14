﻿using System.Linq;
using System.Threading.Tasks;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using System.Threading;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various;

[TestClass]
public class PluginsTest : PluginsTestBase {
  [TestInitialize]
  public async Task SetUp() {
    await SetUpPlugin();
  }

  protected override string LibraryName =>
    "PluginsTest";

  protected override string[] CommandLineArgument =>
    new[] { $@"--dafny:plugins:0={LibraryPath},""because\\ \""whatever""" };

  [TestMethod]
  public async Task EnsureItIsPossibleToLoadAPluginWithArguments() {
    // This code will run with the plugin from PluginsAdvancedTest, but that plugin won't throw an exception on the code below.
    var documentItem = CreateTestDocument("function test(): int { 1 }");
    await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var resolutionReport = await DiagnosticReceiver.AwaitNextNotificationAsync(CancellationToken.None);
    Assert.AreEqual(documentItem.Uri, resolutionReport.Uri);
    var diagnostics = resolutionReport.Diagnostics.ToArray();
    Assert.AreEqual(1 + DafnyOptions.DefaultPlugins.Count, DafnyOptions.O.Plugins.Count,
                    "Not exactly 1 plugin loaded");
    Assert.AreEqual(1, diagnostics.Length, LibraryPath + " did not raise an error.");
    Assert.AreEqual("Impossible to continue because\\ \"whatever", diagnostics[0].Message);
    Assert.AreEqual(new Range((0, 9), (0, 13)), diagnostics[0].Range);
  }

  [TestCleanup]
  public void DoCleanup() {
    CleanupPlugin();
  }
}
