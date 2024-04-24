﻿using System.Linq;
using System.Threading.Tasks;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using System.Threading;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Extensions.DependencyModel;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various;

[TestClass]
public class PluginsAdvancedTest : PluginsTestBase {
  [TestInitialize]
  public async Task SetUp() {
    await SetUpPlugin();
  }

  protected override string LibraryName =>
    "PluginsAdvancedTest";

  protected override string[] CommandLineArgument =>
    new[] { $"--dafny:plugins:0={LibraryPath},force you" };

  [TestMethod]
  public async Task EnsureErrorMessageCanBeComplexAndTakeIntoAccountConfiguration() {
    var documentItem = CreateTestDocument(@"
method {:extern} myMethod(i: int) returns (j: int)

method {:test} myMethodWrongName() {
  var result := myMethod(0);
  expect result == 1;
}
");
    await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var resolutionReport = await DiagnosticReceiver.AwaitNextNotificationAsync(CancellationToken.None);
    Assert.AreEqual(documentItem.Uri, resolutionReport.Uri);
    var diagnostics = resolutionReport.Diagnostics.ToArray();
    Assert.AreEqual(1 + DafnyOptions.DefaultPlugins.Count, DafnyOptions.O.Plugins.Count,
                    "Not exactly 1 plugin loaded");
    Assert.AreEqual(1, diagnostics.Length, LibraryPath + " did not raise an error.");
    Assert.AreEqual("Please declare a method {:test} named myMethod_test that will call myMethod, you", diagnostics[0].Message);
    Assert.AreEqual(new Range((1, 17), (1, 25)), diagnostics[0].Range);
    var related = diagnostics[0].RelatedInformation?.GetEnumerator();
    Assert.IsTrue(related != null && related.MoveNext());
    Assert.AreEqual("You might want to just rename this method", related.Current.Message);
    Assert.AreEqual(new Range((3, 15), (3, 32)), related.Current.Location.Range);
    related.Dispose();
  }

  [TestCleanup]
  public void DoCleanup() {
    CleanupPlugin();
  }
}
