﻿using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization {
  [TestClass]
  public class LookupMigrationTest : SynchronizationTestBase {
    // The assertion Assert.IsFalse(document.SymbolTable.Resolved) is used to ensure that
    // we're working on a migrated symbol table. If that's not the case, the test case has
    // to be adapted.

    [TestMethod]
    public async Task MigrationLeavesLinesOfSymbolsBeforeUnchangedWhenChangingInTheMiddle() {
      var source = @"
class Test {
  var x: int;
  var y: int;

  function GetX(): int
      reads this
  {
    this.x
  }

  function GetConstant(): int
  {
    1
  }

  function GetY(): int
    reads this
  {
    this.y
  }
}".TrimStart();

      var change = @"

  method GetXY() returns (x: int, y: int) {





";
      var documentItem = CreateTestDocument(source);
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangeAndWaitCompletionAsync(
        documentItem,
        new Range((10, 0), (14, 0)),
        change
      );
      var document = await Documents.GetDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      Assert.IsFalse(document.SymbolTable.Resolved);
      Assert.IsTrue(document.SymbolTable.TryGetSymbolAt((7, 10), out var symbol));
      Assert.AreEqual("x", symbol.Name);
    }

    [TestMethod]
    public async Task MigrationLeavesLinesOfSymbolsBeforeUnchangedWhenRemovingInTheMiddle() {
      var source = @"
class Test {
  var x: int;
  var y: int;

  function GetX(): int
      reads this
  {
    this.x
  }

  function GetConstant(): int
  {
    1
  }

  function GetY(): int
    reads this
  {
    this.y
  }
}".TrimStart();

      var change = "";
      var documentItem = CreateTestDocument(source);
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangeAndWaitCompletionAsync(
        documentItem,
        new Range((12, 0), (14, 0)),
        change
      );
      var document = await Documents.GetDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      Assert.IsFalse(document.SymbolTable.Resolved);
      Assert.IsTrue(document.SymbolTable.TryGetSymbolAt((7, 10), out var symbol));
      Assert.AreEqual("x", symbol.Name);
    }

    [TestMethod]
    public async Task MigrationMovesLinesOfSymbolsAfterWhenChangingInTheMiddle() {
      var source = @"
class Test {
  var x: int;
  var y: int;

  function GetX(): int
      reads this
  {
    this.x
  }

  function GetConstant(): int
  {
    1
  }

  function GetY(): int
      reads this
  {
    this.y
  }
}".TrimStart();

      var change = @"

  method GetXY() returns (x: int, y: int) {





";
      var documentItem = CreateTestDocument(source);
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangeAndWaitCompletionAsync(
        documentItem,
        new Range((10, 0), (14, 0)),
        change
      );
      var document = await Documents.GetDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      Assert.IsFalse(document.SymbolTable.Resolved);
      Assert.IsTrue(document.SymbolTable.TryGetSymbolAt((22, 10), out var symbol));
      Assert.AreEqual("y", symbol.Name);
    }

    [TestMethod]
    public async Task MigrationMovesLinesOfSymbolsAfterWhenRemovingInTheMiddle() {
      var source = @"
class Test {
  var x: int;
  var y: int;

  function GetX(): int
      reads this
  {
    this.x
  }

  function GetConstant(): int
  {
    1
  }

  function GetY(): int
    reads this
  {
    this.y
  }
}".TrimStart();

      var change = "";
      var documentItem = CreateTestDocument(source);
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangeAndWaitCompletionAsync(
        documentItem,
        new Range((12, 0), (14, 0)),
        change
      );
      var document = await Documents.GetDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      Assert.IsFalse(document.SymbolTable.Resolved);
      Assert.IsTrue(document.SymbolTable.TryGetSymbolAt((16, 10), out var symbol));
      Assert.AreEqual("y", symbol.Name);
    }

    [TestMethod]
    public async Task MigrationLeavesCharacterOfSymbolsBeforeUnchangedWhenChangingInTheMiddleOfLine() {
      var source = @"
class Test {
  var x: int;

  function GetX(): int
      reads this
  {
    this.x
  }
}".TrimStart();

      var change = " +";
      var documentItem = CreateTestDocument(source);
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangeAndWaitCompletionAsync(
        documentItem,
        new Range((6, 10), (6, 10)),
        change
      );
      var document = await Documents.GetDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      Assert.IsFalse(document.SymbolTable.Resolved);
      Assert.IsTrue(document.SymbolTable.TryGetSymbolAt((6, 10), out var symbol));
      Assert.AreEqual("x", symbol.Name);
    }

    [TestMethod]
    public async Task MigrationMovesCharacterOfSymbolsAfterWhenChangingInTheMiddleOfLine() {
      var source = @"
class Test {
  var x: int;

  function GetX(): int
      reads this
  {
    this.x
  }
}".TrimStart();

      var change = "y + ";
      var documentItem = CreateTestDocument(source);
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangeAndWaitCompletionAsync(
        documentItem,
        new Range((6, 4), (6, 9)),
        change
      );
      var document = await Documents.GetDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      Assert.IsFalse(document.SymbolTable.Resolved);
      Assert.IsTrue(document.SymbolTable.TryGetSymbolAt((6, 9), out var symbol));
      Assert.AreEqual("x", symbol.Name);
    }

    [TestMethod]
    public async Task MigrationRemovesSymbolLocationsWithinTheChangedRange() {
      var source = @"
class Test {
  var x: int;

  function GetX(): int
      reads this
  {
    this.x
  }
}".TrimStart();

      var change = "y + ";
      var documentItem = CreateTestDocument(source);
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var originalDocument = await Documents.GetDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(originalDocument);
      var lookupCountBefore = originalDocument.SymbolTable.LookupTree.Count;

      await ApplyChangeAndWaitCompletionAsync(
        documentItem,
        new Range((6, 9), (6, 10)),
        change
      );
      var document = await Documents.GetDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      Assert.IsFalse(document.SymbolTable.Resolved);
      Assert.IsFalse(document.SymbolTable.TryGetSymbolAt((6, 9), out var _));
      Assert.AreEqual(lookupCountBefore - 1, document.SymbolTable.LookupTree.Count);
    }

    [TestMethod]
    public async Task MigrationMovesSymbolLocationsWhenApplyingMultipleChangesAtOnce() {
      var source = @"
class Test {
  var x: int;

  function GetX(): int
      reads this
  {
    this.x
  }
}".TrimStart();

      var documentItem = CreateTestDocument(source);
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangesAndWaitCompletionAsync(
        documentItem,
        new TextDocumentContentChangeEvent {
          Range = new Range((6, 4), (6, 9)),
          Text = @"this.y
    + "
        },
        new TextDocumentContentChangeEvent {
          Range = new Range((1, 13), (1, 13)),
          Text = @"
  var y: int;

  function GetY(): int {
    this.y
  "
        }
      );
      var document = await Documents.GetDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      Assert.IsFalse(document.SymbolTable.Resolved);
      Assert.IsTrue(document.SymbolTable.TryGetSymbolAt((12, 7), out var symbol));
      Assert.AreEqual("x", symbol.Name);
    }
  }
}
