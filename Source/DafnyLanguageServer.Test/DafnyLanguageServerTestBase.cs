﻿using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Configuration;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.JsonRpc.Testing;
using OmniSharp.Extensions.LanguageProtocol.Testing;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Server;
using OmniSharp.Extensions.LanguageServer.Server;
using System.IO;
using System.IO.Pipelines;
using System.Linq;
using System.Threading.Tasks;
using JetBrains.Annotations;
using MediatR;
using OmniSharp.Extensions.LanguageServer.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Progress;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest {
  public class DafnyLanguageServerTestBase : LanguageServerTestBase {
    protected readonly string SlowToVerify = @"
lemma {:timeLimit 3} SquareRoot2NotRational(p: nat, q: nat)
  requires p > 0 && q > 0
  ensures (p * p) !=  2 * (q * q)
{ 
  if (p * p) ==  2 * (q * q) {
    calc == {
      (2 * q - p) * (2 * q - p);
      4 * q * q + p * p - 4 * p * q;
      {assert 2 * q * q == p * p;}
      2 * q * q + 2 * p * p - 4 * p * q;
      2 * (p - q) * (p - q);
    }
  }
}".TrimStart();

    protected readonly string NeverVerifies = @"
lemma {:neverVerify} HasNeverVerifyAttribute(p: nat, q: nat)
  ensures true
{
}".TrimStart();

    public const string LanguageId = "dafny";
    protected static int fileIndex;

    public ILanguageServer Server { get; private set; }

    public IDocumentDatabase Documents => Server.GetRequiredService<IDocumentDatabase>();

    public DafnyLanguageServerTestBase() : base(new JsonRpcTestOptions(LoggerFactory.Create(
      builder => builder.AddConsole().SetMinimumLevel(LogLevel.Warning)))) { }

    protected virtual async Task<ILanguageClient> InitializeClient(
      Action<LanguageClientOptions> clientOptionsAction = null,
      [CanBeNull] Action<LanguageServerOptions> serverOptionsAction = null) {
      var client = CreateClient(clientOptionsAction, serverOptionsAction);
      await client.Initialize(CancellationToken).ConfigureAwait(false);

      return client;
    }

    protected virtual ILanguageClient CreateClient(
      Action<LanguageClientOptions> clientOptionsAction = null,
      Action<LanguageServerOptions> serverOptionsAction = null) {
      var client = LanguageClient.PreInit(
        options => {
          var (reader, writer) = SetupServer(serverOptionsAction);
          options
            .WithInput(reader)
            .WithOutput(writer)
            .WithLoggerFactory(TestOptions.ClientLoggerFactory)
            .WithAssemblies(TestOptions.Assemblies)
            .WithAssemblies(typeof(LanguageProtocolTestBase).Assembly, GetType().Assembly)
            .ConfigureLogging(x => x.SetMinimumLevel(LogLevel.Trace))
            .WithInputScheduler(options.InputScheduler)
            .WithOutputScheduler(options.OutputScheduler)
            .WithDefaultScheduler(options.DefaultScheduler)
            .Services
            .AddTransient(typeof(IPipelineBehavior<,>), typeof(SettlePipeline<,>))
            .AddSingleton(Events as IRequestSettler);

          clientOptionsAction?.Invoke(options);
        }
      );

      Disposable.Add(client);

      return client;
    }

    protected (Stream clientOutput, Stream serverInput) SetupServer(
      Action<LanguageServerOptions> serverOptionsAction = null) {
      var clientPipe = new Pipe(TestOptions.DefaultPipeOptions);
      var serverPipe = new Pipe(TestOptions.DefaultPipeOptions);
      Server = OmniSharp.Extensions.LanguageServer.Server.LanguageServer.PreInit(
        options => {
          var configuration = CreateConfiguration();
          options
            .WithInput(serverPipe.Reader)
            .WithOutput(clientPipe.Writer)
            .ConfigureLogging(SetupTestLogging)
            .WithDafnyLanguageServer(configuration, () => { });
          serverOptionsAction?.Invoke(options);
        });
      // This is the style used in the LSP implementation itself:
      // https://github.com/OmniSharp/csharp-language-server-protocol/blob/1b6788df2600083c28811913a221ccac7b1d72c9/test/Lsp.Tests/Testing/LanguageServerTestBaseTests.cs
#pragma warning disable VSTHRD110 // Observe result of async calls
      Server.Initialize(CancellationToken);
#pragma warning restore VSTHRD110 // Observe result of async calls
      return (clientPipe.Reader.AsStream(), serverPipe.Writer.AsStream());
    }

    protected virtual IConfiguration CreateConfiguration() {
      var configurationBuilder = new ConfigurationBuilder();
      return configurationBuilder.Build();
    }

    private static void SetupTestLogging(ILoggingBuilder builder) {
      builder
        .AddFilter("OmniSharp", LogLevel.Warning)
        .AddFilter("Microsoft.Dafny", LogLevel.Debug)
        .SetMinimumLevel(LogLevel.Debug)
        .AddConsole();
    }

    protected static TextDocumentItem CreateTestDocument(string source, string filePath = null, int version = 1) {
      filePath ??= $"testFile{fileIndex++}.dfy";
      return new TextDocumentItem {
        LanguageId = LanguageId,
        Text = source,
        Uri = filePath.StartsWith("untitled:") ? DocumentUri.Parse(filePath) : DocumentUri.FromFileSystemPath(filePath),
        Version = version
      };
    }

    protected static void OpenDocument(ILanguageClient client, TextDocumentItem document) {
      client.DidOpenTextDocument(new DidOpenTextDocumentParams {
        TextDocument = document
      });
    }

    public static string PrintDiagnostics(IEnumerable<Diagnostic> items) {
      return PrintEnumerable(items.Select(PrintDiagnostic));
    }

    public static string PrintDiagnostic(Diagnostic diagnostic) {
      var relatedPrint = string.Join(", ", diagnostic.RelatedInformation?.
        Select(r => $"at {r.Location} saying '{r.Message}'") ?? Array.Empty<string>());
      return $"Diagnostic at {diagnostic.Range} saying '{diagnostic.Message}', related: {relatedPrint}";
    }

    public static string PrintEnumerable(IEnumerable<object> items) {
      return "[" + string.Join(", ", items.Select(o => o.ToString())) + "]";
    }

    protected override (Stream clientOutput, Stream serverInput) SetupServer() {
      throw new NotImplementedException();
    }

    protected async Task WithNoopSolver(Func<Task> action) {
      var oldProverOptions = DafnyOptions.O.ProverOptions.ToImmutableList();
      DafnyOptions.O.ProverOptions.Add("SOLVER=noop");
      await action();
      DafnyOptions.O.ProverOptions = oldProverOptions.ToList();
    }
  }
}
