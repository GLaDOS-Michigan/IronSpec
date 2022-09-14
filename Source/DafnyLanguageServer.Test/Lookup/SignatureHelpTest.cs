﻿using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Lookup {
  [TestClass]
  public class SignatureHelpTest : ClientBasedLanguageServerTest {

    private Task<SignatureHelp> RequestSignatureHelpAsync(TextDocumentItem documentItem, Position position) {
      // TODO at this time we do not set the context since it appears that's also the case when used within VSCode.
      return client.RequestSignatureHelp(
        new SignatureHelpParams {
          TextDocument = documentItem.Uri,
          Position = position
        },
        CancellationToken
      );
    }

    [TestMethod]
    public async Task SignatureHelpForUnloadedDocumentReturnsNull() {
      var documentItem = CreateTestDocument("");
      var signatureHelp = await RequestSignatureHelpAsync(documentItem, (7, 11));
      Assert.IsNull(signatureHelp);
    }

    [TestMethod]
    public async Task SignatureHelpOnOpeningParenthesesReturnsSignatureForExistingMethod() {
      var source = @"
method Multiply(x: int, y: int) returns (p: int)
  ensures p == x * y
{
  return x * y;
}

method Main() {
  //
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      ApplyChange(
        ref documentItem,
          new Range((7, 2), (7, 2)),
          "Multiply("
      );

      var signatureHelp = await RequestSignatureHelpAsync(documentItem, (7, 11));
      var signatures = signatureHelp.Signatures.ToArray();
      Assert.AreEqual(1, signatures.Length);
      var markup = signatures[0].Documentation.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nmethod Multiply(x: int, y: int) returns (p: int)\n```", markup.Value);
    }

    [TestMethod]
    public async Task SignatureHelpOnOpeningParenthesesReturnsSignatureForExistingFunction() {
      var source = @"
function Multiply(x: int, y: int): int
{
  x * y
}

method Main() {
  //
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      ApplyChange(
        ref documentItem,
          new Range((6, 2), (6, 2)),
          "Multiply("
      );

      var signatureHelp = await RequestSignatureHelpAsync(documentItem, (6, 11));
      var signatures = signatureHelp.Signatures.ToArray();
      Assert.AreEqual(1, signatures.Length);
      var markup = signatures[0].Documentation.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nfunction Multiply(x: int, y: int): int\n```", markup.Value);
    }

    [TestMethod]
    public async Task SignatureHelpOnOpeningParenthesesReturnsNullIfNoSuchMethodOrFunctionExists() {
      var source = @"
method Main() {
  //
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      ApplyChange(
        ref documentItem,
          new Range((1, 2), (1, 2)),
          "Multiply("
      );

      var signatureHelp = await RequestSignatureHelpAsync(documentItem, (1, 11));
      Assert.IsNull(signatureHelp);
    }

    [TestMethod]
    public async Task SignatureHelpOnOpeningParenthesesReturnsSignatureOfClosestFunction() {
      var source = @"
function Multiply(x: int, y: int): int
{
  x * y
}

module Mod {
  function Multiply(a: int, b: int): int
  {
    a * b
  }

  class SomeClass {
    function Multiply(n: int, m: int): int
    {
      n * m
    }

    method GetProduct(x: int, y: int) returns (p: int)
      ensures p == x * y
    {
      //
    }
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      ApplyChange(
        ref documentItem,
          new Range((20, 6), (20, 6)),
          "Multiply("
      );

      var signatureHelp = await RequestSignatureHelpAsync(documentItem, (20, 15));
      var signatures = signatureHelp.Signatures.ToArray();
      Assert.AreEqual(1, signatures.Length);
      var markup = signatures[0].Documentation.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nfunction SomeClass.Multiply(n: int, m: int): int\n```", markup.Value);
    }

    [TestMethod]
    public async Task SignatureHelpOnOpeningParenthesesReturnsSignatureOfClassMemberOfDesignator() {
      var source = @"
class A {
  constructor() {}

  function Multiply(n: int, m: int): int
  {
    n * m
  }
}


class B {
  var a: A;

  constructor() {
    a := new A();
  }

  function Multiply(x: int, y: int): int
  {
    x * y
  }

  method GetProduct(x: int, y: int) returns (p: int)
    ensures p == x * y
  {
    //
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      ApplyChange(
        ref documentItem,
          new Range((25, 4), (25, 4)),
          "a.Multiply("
      );

      var signatureHelp = await RequestSignatureHelpAsync(documentItem, (25, 15));
      var signatures = signatureHelp.Signatures.ToArray();
      Assert.AreEqual(1, signatures.Length);
      var markup = signatures[0].Documentation.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nfunction A.Multiply(n: int, m: int): int\n```", markup.Value);
    }
  }
}
