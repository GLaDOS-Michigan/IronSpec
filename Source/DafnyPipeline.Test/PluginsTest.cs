﻿using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Xunit;
using Microsoft.Dafny;

namespace DafnyPipeline.Test;

[Collection("Dafny plug-ins tests")]
public class PluginsTest {
  /// <summary>
  /// This method creates a library and returns the path to that library.
  /// The library extends a Rewriter so that we can verify that Dafny invokes it if provided in argument.
  /// </summary>
  private string GetLibrary(string name) {
    var assembly = Assembly.GetExecutingAssembly();
    Stream codeStream = assembly.GetManifestResourceStream($"DafnyPipeline.Test._plugins.{name}.cs");
    Assert.NotNull(codeStream);
    string code = new StreamReader(codeStream).ReadToEnd();

    var temp = Path.GetTempFileName();
    var compilation = CSharpCompilation.Create(name);
    var standardLibraries = new List<string>()
    {
      "DafnyPipeline",
      "System.Runtime",
      "Boogie.Core"
    };
    compilation = compilation.AddReferences(standardLibraries.Select(fileName =>
        MetadataReference.CreateFromFile(Assembly.Load(fileName).Location)))
      .AddReferences(
        MetadataReference.CreateFromFile(typeof(object).GetTypeInfo().Assembly.Location))
      .WithOptions(
        new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary)
      );
    var syntaxTree = CSharpSyntaxTree.ParseText(code);
    compilation = compilation.AddSyntaxTrees(syntaxTree);
    var assemblyPath = $"{temp}.dll";
    var result = compilation.Emit(assemblyPath);

    Assert.True(result.Success, string.Join("\n", result.Diagnostics.Select(d => d.ToString())));
    return assemblyPath;
  }

  class CollectionErrorReporter : BatchErrorReporter {
    public string GetLastErrorMessage() {
      return AllMessages[ErrorLevel.Error][0].message;
    }
  }

  [Fact]
  public void EnsurePluginIsExecuted() {
    var library = GetLibrary("rewriterPreventingVerificationWithArgument");

    var reporter = new CollectionErrorReporter();
    var options = DafnyOptions.Create();
    options.Plugins.Add(AssemblyPlugin.Load(library, new string[] { "because whatever" }));
    DafnyOptions.Install(options);

    var programString = "function test(): int { 1 }";
    ModuleDecl module = new LiteralModuleDecl(new DefaultModuleDecl(), null);
    Microsoft.Dafny.Type.ResetScopes();
    BuiltIns builtIns = new BuiltIns();
    Parser.Parse(programString, "virtual", "virtual", module, builtIns, reporter);
    var dafnyProgram = new Program("programName", module, builtIns, reporter);
    Main.Resolve(dafnyProgram, reporter);

    Assert.Equal(1, reporter.Count(ErrorLevel.Error));
    Assert.Equal("Impossible to continue because whatever", reporter.GetLastErrorMessage());
  }

  [Fact]
  public void EnsurePluginIsExecutedEvenWithoutConfiguration() {
    var library = GetLibrary("rewriterPreventingVerification");

    var reporter = new CollectionErrorReporter();
    var options = DafnyOptions.Create();
    options.Plugins.Add(AssemblyPlugin.Load(library, new string[] { "ignored arguments" }));
    DafnyOptions.Install(options);

    var programString = "function test(): int { 1 }";
    var dafnyProgram = CreateProgram(programString, reporter);
    Main.Resolve(dafnyProgram, reporter);
    Assert.Equal(1, reporter.ErrorCount);
    Assert.Equal("Impossible to continue", reporter.GetLastErrorMessage());
  }

  [Fact]
  public void EnsurePluginIsExecutedAndAllowsVerification() {
    var library = GetLibrary("rewriterAllowingVerification");

    var reporter = new CollectionErrorReporter();
    var options = DafnyOptions.Create();
    options.Plugins.Add(AssemblyPlugin.Load(library, new string[] { "ignored arguments" }));
    DafnyOptions.Install(options);

    var programString = "function test(): int { 1 }";
    var dafnyProgram = CreateProgram(programString, reporter);
    Main.Resolve(dafnyProgram, reporter);
    Assert.Equal(0, reporter.ErrorCountUntilResolver);
    Assert.Equal(1, reporter.ErrorCount);
  }

  private static Program CreateProgram(string programString, CollectionErrorReporter reporter) {
    ModuleDecl module = new LiteralModuleDecl(new DefaultModuleDecl(), null);
    Type.ResetScopes();
    BuiltIns builtIns = new BuiltIns();
    Parser.Parse(programString, "virtual", "virtual", module, builtIns, reporter);
    var dafnyProgram = new Program("programName", module, builtIns, reporter);
    return dafnyProgram;
  }
}
