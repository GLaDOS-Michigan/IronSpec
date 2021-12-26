﻿using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Configuration;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization {
  [TestClass]
  public class DiagnosticsTest : DafnyLanguageServerTestBase {
    // TODO test locations as well?
    private ILanguageClient client;
    private TestNotificationReceiver<PublishDiagnosticsParams> diagnosticReceiver;
    private IDictionary<string, string> configuration;

    [TestInitialize]
    public Task SetUp() => SetUp(null);

    public async Task SetUp(IDictionary<string, string> configuration) {
      this.configuration = configuration;
      diagnosticReceiver = new();
      client = await InitializeClient(options => options.OnPublishDiagnostics(diagnosticReceiver.NotificationReceived));
    }

    protected override IConfiguration CreateConfiguration() {
      return configuration == null
        ? base.CreateConfiguration()
        : new ConfigurationBuilder().AddInMemoryCollection(configuration).Build();
    }

    [TestMethod]
    public async Task OpeningFlawlessDocumentReportsEmptyDiagnostics() {
      var source = @"
method Multiply(x: int, y: int) returns (product: int)
  requires y >= 0 && x >= 0
  decreases y
  ensures product == x * y && product >= 0
{
  if y == 0 {
    product := 0;
  } else {
    var step := Multiply(x, y - 1);
    product := x + step;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var report = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(0, diagnostics.Length);
    }

    [TestMethod]
    public async Task OpeningDocumentWithSyntaxErrorReportsDiagnosticsWithParserErrors() {
      var source = @"
method Multiply(x: int, y: int) returns (product: int
  requires y >= 0 && x >= 0
  decreases y
  ensures product == x * y && product >= 0
{
  if y == 0 {
    product := 0;
  } else {
    var step := Multiply(x, y - 1);
    product := x + step;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var report = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(1, diagnostics.Length);
      Assert.AreEqual("Parser", diagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[0].Severity);
    }

    [TestMethod]
    public async Task OpeningDocumentWithSemanticErrorReportsDiagnosticsWithSemanticErrors() {
      var source = @"
method Multiply(x: int, y: int) returns (product: int)
  requires y >= 0 && x >= 0
  decreases y
  ensures product == x * y && product >= 0
{
  if y == 0 {
    product := 0;
  } else {
    var step := Multiply(x, y - ""1"");
    product := x + step;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var report = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(1, diagnostics.Length);
      Assert.AreEqual("Resolver", diagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[0].Severity);
    }

    [TestMethod]
    public async Task OpeningDocumentWithMultipleSemanticErrorsReportsDiagnosticsWithAllSemanticErrors() {
      var source = @"
method Multiply(x: int, y: int) returns (product: int)
  requires y >= 0 && x >= 0
  decreases y
  ensures product == x * y && product >= 0
{
  if y == ""0"" {
    product := 0;
  } else {
    var step := Multiply(x, y - ""1"");
    product := x + step;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var report = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(2, diagnostics.Length);
      Assert.AreEqual("Resolver", diagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[0].Severity);
      Assert.AreEqual("Resolver", diagnostics[1].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[1].Severity);
    }

    [TestMethod]
    public async Task OpeningDocumentWithVerificationErrorReportsDiagnosticsWithVerificationErrors() {
      var source = @"
method Multiply(x: int, y: int) returns (product: int)
  requires x >= 0
  decreases y
  ensures product == x * y && product >= 0
{
  if y == 0 {
    product := 0;
  } else {
    var step := Multiply(x, y - 1);
    product := x + step;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var report = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(1, diagnostics.Length);
      Assert.AreEqual("Other", diagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[0].Severity);
    }

    [TestMethod]
    public async Task OpeningDocumentWithVerificationErrorDoesNotReportDiagnosticsWithVerificationErrorsIfNotVerifyOnChange() {
      var source = @"
method Multiply(x: int, y: int) returns (product: int)
  requires x >= 0
  decreases y
  ensures product == x * y && product >= 0
{
  if y == 0 {
    product := 0;
  } else {
    var step := Multiply(x, y - 1);
    product := x + step;
  }
}".TrimStart();
      await SetUp(new Dictionary<string, string>() {
        { $"{DocumentOptions.Section}:{nameof(DocumentOptions.Verify)}", nameof(AutoVerification.Never) }
      });
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var report = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(0, diagnostics.Length);
    }

    [TestMethod]
    public async Task OpeningDocumentWithMultipleVerificationErrorsReportsDiagnosticsWithAllVerificationErrorsAndRelatedInformation() {
      var source = @"
method Multiply(x: int, y: int) returns (product: int)
  decreases y
  ensures product == x * y && product >= 0
{
  if y == 0 {
    product := 0;
  } else {
    var step := Multiply(x, y - 1);
    product := x + step;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var report = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(2, diagnostics.Length);
      Assert.AreEqual("Other", diagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[0].Severity);
      Assert.AreEqual("Other", diagnostics[1].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[1].Severity);
      Assert.AreEqual(1, diagnostics[0].RelatedInformation.Count());
      var relatedInformation = diagnostics[0].RelatedInformation.First();
      Assert.AreEqual("This is the postcondition that might not hold.", relatedInformation.Message);
      Assert.AreEqual(new Range(new Position(2, 38), new Position(2, 40)), relatedInformation.Location.Range);
    }

    [TestMethod]
    public async Task ChangingCorrectDocumentToOneWithSyntaxErrorsReportsTheSyntaxErrors() {
      var source = @"
method Multiply(x: int, y: int) returns (product: int)
  requires y >= 0 && x >= 0
  decreases y
  ensures product == x * y && product >= 0
{
  if y == 0 {
    product := 0;
  } else {
    var step := Multiply(x, y - 1);
    product := x + step;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var reportAfterOpening = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationToken);
      var diagnosticsAfterOpening = reportAfterOpening.Diagnostics.ToArray();
      Assert.AreEqual(0, diagnosticsAfterOpening.Length);

      client.DidChangeTextDocument(new DidChangeTextDocumentParams {
        TextDocument = new OptionalVersionedTextDocumentIdentifier {
          Uri = documentItem.Uri,
          Version = documentItem.Version + 1
        },
        ContentChanges = new[] {
          new TextDocumentContentChangeEvent {
            Range = new Range((0, 53), (0, 54)),
            Text = ""
          }
        }
      });

      var report = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(1, diagnostics.Length);
      Assert.AreEqual("Parser", diagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[0].Severity);
    }

    [TestMethod]
    public async Task ChangingCorrectDocumentToOneWithSyntaxErrorsReportsTheSyntaxErrorsIfNotVerifyOnChange() {
      var source = @"
method Multiply(x: int, y: int) returns (product: int)
  requires y >= 0 && x >= 0
  decreases y
  ensures product == x * y && product >= 0
{
  if y == 0 {
    product := 0;
  } else {
    var step := Multiply(x, y - 1);
    product := x + step;
  }
}".TrimStart();
      await SetUp(new Dictionary<string, string>() {
        { $"{DocumentOptions.Section}:{nameof(DocumentOptions.Verify)}", nameof(AutoVerification.Never) }
      });
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var reportAfterOpening = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationToken);
      var diagnosticsAfterOpening = reportAfterOpening.Diagnostics.ToArray();
      Assert.AreEqual(0, diagnosticsAfterOpening.Length);

      client.DidChangeTextDocument(new DidChangeTextDocumentParams {
        TextDocument = new OptionalVersionedTextDocumentIdentifier {
          Uri = documentItem.Uri,
          Version = documentItem.Version + 1
        },
        ContentChanges = new[] {
          new TextDocumentContentChangeEvent {
            Range = new Range((0, 53), (0, 54)),
            Text = ""
          }
        }
      });

      var report = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(1, diagnostics.Length);
      Assert.AreEqual("Parser", diagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[0].Severity);
    }

    [TestMethod]
    public async Task ChangingCorrectDocumentToOneWithVerificationErrorsReportsTheVerificationErrors() {
      var source = @"
method Multiply(x: int, y: int) returns (product: int)
  requires y >= 0 && x >= 0
  decreases y
  ensures product == x * y && product >= 0
{
  if y == 0 {
    product := 0;
  } else {
    var step := Multiply(x, y - 1);
    product := x + step;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var reportAfterOpening = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationToken);
      var diagnosticsAfterOpening = reportAfterOpening.Diagnostics.ToArray();
      Assert.AreEqual(0, diagnosticsAfterOpening.Length);

      client.DidChangeTextDocument(new DidChangeTextDocumentParams {
        TextDocument = new OptionalVersionedTextDocumentIdentifier {
          Uri = documentItem.Uri,
          Version = documentItem.Version + 1
        },
        ContentChanges = new[] {
          new TextDocumentContentChangeEvent {
            Range = new Range((8, 30), (8, 31)),
            Text = "+"
          }
        }
      });

      var report = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(1, diagnostics.Length);
      Assert.AreEqual("Other", diagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[0].Severity);
    }

    [TestMethod]
    public async Task ChangingCorrectDocumentToOneWithVerificationErrorsDoesNotReportVerificationErrorsIfNotVerifyOnChange() {
      var source = @"
method Multiply(x: int, y: int) returns (product: int)
  requires y >= 0 && x >= 0
  decreases y
  ensures product == x * y && product >= 0
{
  if y == 0 {
    product := 0;
  } else {
    var step := Multiply(x, y - 1);
    product := x + step;
  }
}".TrimStart();
      await SetUp(new Dictionary<string, string>() {
        { $"{DocumentOptions.Section}:{nameof(DocumentOptions.Verify)}", nameof(AutoVerification.Never) }
      });
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var reportAfterOpening = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationToken);
      var diagnosticsAfterOpening = reportAfterOpening.Diagnostics.ToArray();
      Assert.AreEqual(0, diagnosticsAfterOpening.Length);

      client.DidChangeTextDocument(new DidChangeTextDocumentParams {
        TextDocument = new OptionalVersionedTextDocumentIdentifier {
          Uri = documentItem.Uri,
          Version = documentItem.Version + 1
        },
        ContentChanges = new[] {
          new TextDocumentContentChangeEvent {
            Range = new Range((8, 30), (8, 31)),
            Text = "+"
          }
        }
      });

      var report = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(0, diagnostics.Length);
    }

    [TestMethod]
    public async Task ApplyingMultipleChangesInDocumentOnlySendsOneReport() {
      var source = @"
method Multiply(x: int, y: int) returns (product: int)
  requires y >= 0 && x >= 0
  decreases y
  ensures product == x * y && product >= 0
{
  if y == 0 {
    product := 0;
  } else {
    var step := Multiply(x, y - 1);
    product := x + step;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var reportAfterOpening = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationToken);
      var diagnosticsAfterOpening = reportAfterOpening.Diagnostics.ToArray();
      Assert.AreEqual(0, diagnosticsAfterOpening.Length);

      client.DidChangeTextDocument(new DidChangeTextDocumentParams {
        TextDocument = new OptionalVersionedTextDocumentIdentifier {
          Uri = documentItem.Uri,
          Version = documentItem.Version + 1
        },
        ContentChanges = new[] {
          new TextDocumentContentChangeEvent {
            Range = new Range((0, 53), (0, 54)),
            Text = ""
          },
          new TextDocumentContentChangeEvent {
            Range = new Range((0, 53), (0, 53)),
            Text = ")"
          }
        }
      });

      // The test applies a change that introduces a syntax error and fixes it thereafter.
      // Therefore, we know that the erronoues state was never reported when we now receive
      // a report without any diagnostics/errors.
      // Otherwise, we'd have to wait for a signal/diagnostic that should never be sent, e.g.
      // with a timeout.
      var report = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(0, diagnostics.Length);
    }

    [TestMethod]
    public async Task ClosingDocumentWithSyntaxErrorHidesDiagnosticsBySendingEmptyDiagnostics() {
      var source = @"
method Multiply(x: int, y: int) returns (product: int
  requires y >= 0 && x >= 0
  decreases y
  ensures product == x * y && product >= 0
{
  if y == 0 {
    product := 0;
  } else {
    var step := Multiply(x, y - 1);
    product := x + step;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await diagnosticReceiver.AwaitNextNotificationAsync(CancellationToken);
      client.DidCloseTextDocument(new DidCloseTextDocumentParams { TextDocument = documentItem });
      var report = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(0, diagnostics.Length);
    }

    [TestMethod]
    public async Task OpeningDocumentThatIncludesNonExistantDocumentReportsParserErrorAtInclude() {
      var source = "include \"doesNotExist.dfy\"";
      var documentItem = CreateTestDocument(source, Path.Combine(Directory.GetCurrentDirectory(), "Synchronization/TestFiles/test.dfy"));
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var report = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(1, diagnostics.Length);
      Assert.AreEqual("Parser", diagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[0].Severity);
      Assert.AreEqual(new Range((0, 8), (0, 26)), diagnostics[0].Range);
    }

    [TestMethod]
    public async Task OpeningDocumentThatIncludesDocumentWithSyntaxErrorsReportsParserErrorAtInclude() {
      var source = "include \"syntaxError.dfy\"";
      var documentItem = CreateTestDocument(source, Path.Combine(Directory.GetCurrentDirectory(), "Synchronization/TestFiles/test.dfy"));
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var report = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(1, diagnostics.Length);
      Assert.AreEqual("Parser", diagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[0].Severity);
      Assert.AreEqual(new Range((0, 8), (0, 25)), diagnostics[0].Range);
    }

    [TestMethod]
    public async Task OpeningDocumentThatIncludesDocumentWithSemanticErrorsReportsResolverErrorAtInclude() {
      var source = "include \"syntaxError.dfy\"";
      var documentItem = CreateTestDocument(source, Path.Combine(Directory.GetCurrentDirectory(), "Synchronization/TestFiles/test.dfy"));
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var report = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(1, diagnostics.Length);
      Assert.AreEqual("Parser", diagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[0].Severity);
      Assert.AreEqual(new Range((0, 8), (0, 25)), diagnostics[0].Range);
    }

    [TestMethod]
    public async Task OpeningDocumentWithSemanticErrorsInIncludeReportsResolverErrorAtIncludeStatement() {
      var source = "include \"semanticError.dfy\"";
      var documentItem = CreateTestDocument(source, Path.Combine(Directory.GetCurrentDirectory(), "Synchronization/TestFiles/test.dfy"));
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var report = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(1, diagnostics.Length);
      Assert.AreEqual("Resolver", diagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[0].Severity);
      Assert.AreEqual(new Range((0, 8), (0, 27)), diagnostics[0].Range);
    }

    [TestMethod]
    public async Task SavingDocumentWithVerificationErrorDoesNotDiscardDiagnosticsWithVerificationErrorsIfVerifyOnChange() {
      var source = @"
method Multiply(x: int, y: int) returns (product: int)
  requires x >= 0
  decreases y
  ensures product == x * y && product >= 0
{
  if y == 0 {
    product := 0;
  } else {
    var step := Multiply(x, y - 1);
    product := x + step;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var changeReport = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationToken);
      var changeDiagnostics = changeReport.Diagnostics.ToArray();
      Assert.AreEqual(1, changeDiagnostics.Length);
      Assert.AreEqual("Other", changeDiagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, changeDiagnostics[0].Severity);
      client.SaveDocument(documentItem);
      var saveReport = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationToken);
      var saveDiagnostics = saveReport.Diagnostics.ToArray();
      Assert.AreEqual(1, saveDiagnostics.Length);
      Assert.AreEqual("Other", saveDiagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, saveDiagnostics[0].Severity);
    }

    [TestMethod]
    public async Task SavingDocumentWithVerificationErrorReportsDiagnosticsWithVerificationErrorsIfVerifyOnSave() {
      var source = @"
method Multiply(x: int, y: int) returns (product: int)
  requires x >= 0
  decreases y
  ensures product == x * y && product >= 0
{
  if y == 0 {
    product := 0;
  } else {
    var step := Multiply(x, y - 1);
    product := x + step;
  }
}".TrimStart();
      await SetUp(new Dictionary<string, string>() {
        { $"{DocumentOptions.Section}:{nameof(DocumentOptions.Verify)}", nameof(AutoVerification.OnSave) }
      });
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var changeReport = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationToken);
      var changeDiagnostics = changeReport.Diagnostics.ToArray();
      Assert.AreEqual(0, changeDiagnostics.Length);
      client.SaveDocument(documentItem);
      var saveReport = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationToken);
      var saveDiagnostics = saveReport.Diagnostics.ToArray();
      Assert.AreEqual(1, saveDiagnostics.Length);
      Assert.AreEqual("Other", saveDiagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, saveDiagnostics[0].Severity);
    }

    [TestMethod]
    public async Task OpeningDocumentWithVerificationErrorReportsDiagnosticsWithVerificationErrorsAndNestedRelatedLocations() {
      var source = @"
class Test {
    var a: nat
    var b: nat
    var c: nat

    predicate Valid()
        reads this
    {
        && a < b
        && b < c
    }

    method Foo()
        requires Valid()
        ensures Valid()
        modifies this
    {
        c := 10;
    }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      client.OpenDocument(documentItem);
      var report = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(1, diagnostics.Length);
      Assert.AreEqual("Other", diagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[0].Severity);
      var relatedInformation = diagnostics[0].RelatedInformation.ToArray();
      Assert.AreEqual(2, relatedInformation.Length);
      Assert.AreEqual("This is the postcondition that might not hold.", relatedInformation[0].Message);
      Assert.AreEqual(new Range((14, 16), (14, 21)), relatedInformation[0].Location.Range);
      Assert.AreEqual("Related location", relatedInformation[1].Message);
      Assert.AreEqual(new Range((9, 13), (9, 14)), relatedInformation[1].Location.Range);
    }

    [TestMethod]
    public async Task OpeningDocumentWithMultipleVerificationCoresReturnsStableDiagnostics() {
      var source = @"
method t0() { assert true; }
method t1() { assert true; }
method t2() { assert true; }
method t3() { assert true; }
method t4() { assert true; }
method t5() { assert true; }
method t6() { assert false; }
method t7() { assert false; }
method t8() { assert false; }
method t9() { assert false; }
method t10() { assert false; }".TrimStart();
      await SetUp(new Dictionary<string, string>() {
        { $"{VerifierOptions.Section}:{nameof(VerifierOptions.VcsCores)}", "4" }
      });
      for (int i = 0; i < 20; i++) {
        var documentItem = CreateTestDocument(source, $"test_{i}.dfy");
        client.OpenDocument(documentItem);
        var report = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationToken);
        var diagnostics = report.Diagnostics.ToArray();
        Assert.AreEqual(5, diagnostics.Length);
        Assert.AreEqual("Other", diagnostics[0].Source);
        Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[0].Severity);
      }
    }
  }
}
