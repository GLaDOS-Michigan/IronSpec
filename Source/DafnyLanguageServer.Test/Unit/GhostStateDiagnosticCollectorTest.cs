﻿using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using IntervalTree;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Options;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using Moq;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Unit; 

[TestClass]
public class GhostStateDiagnosticCollectorTest {
  private GhostStateDiagnosticCollector ghostStateDiagnosticCollector;

  class DummyOptions : IOptions<GhostOptions> {
    public GhostOptions Value { get; set; }
  }

  class DummyLogger : ILogger<GhostStateDiagnosticCollector> {
    public void Log<TState>(LogLevel logLevel, EventId eventId, TState state, Exception exception, Func<TState, Exception, string> formatter) {
      // Do nothing
    }

    public bool IsEnabled(LogLevel logLevel) {
      return true;
    }

    public IDisposable BeginScope<TState>(TState state) {
      return null;
    }
  }

  [TestInitialize]
  public void SetUp() {
    var loggerFactory = new Mock<ILoggerFactory>();
    var options = new DummyOptions {
      Value = new Mock<GhostOptions>().Object
    };
    options.Value.MarkStatements = true;
    ghostStateDiagnosticCollector = new GhostStateDiagnosticCollector(
      options,
      new DummyLogger());
  }

  class CollectingErrorReporter : BatchErrorReporter {
    public Dictionary<ErrorLevel, List<ErrorMessage>> GetErrors() {
      return this.AllMessages;
    }
  }

  class DummyModuleDecl : LiteralModuleDecl {
    public DummyModuleDecl() : base(
      new DefaultModuleDecl(), null) {
    }
    public override object Dereference() {
      return this;
    }
  }

  [TestMethod]
  public void EnsureResilienceAgainstErrors() {
    // Builtins is null to trigger an error.
    var reporter = new CollectingErrorReporter();
    var program = new Dafny.Program("dummy", new DummyModuleDecl(), null, reporter);
    var ghostDiagnostics = ghostStateDiagnosticCollector.GetGhostStateDiagnostics(
      new SymbolTable(null!, new CompilationUnit(program), null!, null!, new IntervalTree<Position, ILocalizableSymbol>(), true)
      , CancellationToken.None);
    Assert.AreEqual(0, ghostDiagnostics.Count());
  }
}