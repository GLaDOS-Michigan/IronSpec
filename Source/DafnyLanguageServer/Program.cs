﻿using Microsoft.Extensions.Configuration;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Server;
using Serilog;
using System;
using System.IO;
using System.Reflection;
using System.Text;
using System.Threading.Tasks;
using Serilog.Events;
using OmniSharpLanguageServer = OmniSharp.Extensions.LanguageServer.Server.LanguageServer;

namespace Microsoft.Dafny.LanguageServer {
  public class Program {
    private static async Task Main(string[] args) {
      var configuration = CreateConfiguration(args);
      InitializeLogger(configuration);
      try {
        Action? shutdownServer = null;
        var server = await OmniSharpLanguageServer.From(
          options => options
            .WithInput(Console.OpenStandardInput())
            .WithOutput(Console.OpenStandardOutput())
            .ConfigureConfiguration(builder => builder.AddConfiguration(configuration))
            .ConfigureLogging(SetupLogging)
            .WithUnhandledExceptionHandler(LogException)
            // ReSharper disable once AccessToModifiedClosure
            .WithDafnyLanguageServer(configuration, () => shutdownServer!())
        );
        // Prevent any other parts of the language server to actually write to standard output.
        await using var logWriter = new LogWriter();
        Console.SetOut(logWriter);
        shutdownServer = () => server.ForcefulShutdown();
        await server.WaitForExit;
      }
      finally {
        Log.CloseAndFlush();
      }
    }

    private static IConfiguration CreateConfiguration(string[] args) {
      return new ConfigurationBuilder()
        .AddJsonFile("DafnyLanguageServer.appsettings.json", optional: true)
        .AddCommandLine(args)
        .Build();
    }

    private static void InitializeLogger(IConfiguration configuration) {
      // The environment variable is used so a log file can be explicitly created in the application dir.
      Environment.SetEnvironmentVariable("DAFNYLS_APP_DIR", Path.GetDirectoryName(Assembly.GetExecutingAssembly().Location));
      Log.Logger = new LoggerConfiguration()
        .ReadFrom.Configuration(configuration)
        .CreateLogger();
    }

    private static void LogException(Exception exception) {
      Log.Logger.Error(exception, "captured unhandled exception");
    }

    private static void SetupLogging(ILoggingBuilder builder) {
      builder
        .ClearProviders()
        .AddSerilog(Log.Logger);
    }

    private class LogWriter : TextWriter {
      public override void Write(char value) {
        Log.Logger.Verbose("Unexpected console output: {value}", value);
      }

      public override void Write(string? value) {
        Log.Logger.Verbose("Unexpected console output: {value}", value);
      }

      public override Encoding Encoding { get; } = Encoding.ASCII;
    }
  }
}
