using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Text;
using Xunit.Abstractions;

namespace XUnitExtensions.Lit {
  public class MainMethodLitCommand : ILitCommand {
    private readonly Assembly assembly;
    private readonly string[] arguments;

    private MainMethodLitCommand(Assembly assembly, string[] arguments) {
      this.assembly = assembly;
      this.arguments = arguments;
    }

    public static ILitCommand Parse(Assembly assembly, IEnumerable<string> arguments, LitTestConfiguration config, bool invokeDirectly) {
      var result = new MainMethodLitCommand(assembly, arguments.ToArray());
      return invokeDirectly ? result : result.ToShellCommand(config);
    }

    public (int, string, string) Execute(ITestOutputHelper outputHelper, TextReader? inputReader, TextWriter? outputWriter, TextWriter? errorWriter) {
      if (inputReader != null) {
        Console.SetIn(inputReader);
      }
      if (outputWriter != null) {
        Console.SetOut(outputWriter);
      }
      if (errorWriter != null) {
        Console.SetError(errorWriter);
      }

      var exitCode = (int)assembly.EntryPoint!.Invoke(null, new object[] { arguments })!;

      return (exitCode, "", "");
    }

    public ILitCommand ToShellCommand(LitTestConfiguration config) {
      var shellArguments = new[] { assembly.Location }.Concat(arguments);
      return new ShellLitCommand(config, "dotnet", shellArguments, config.PassthroughEnvironmentVariables);
    }

    public override string ToString() {
      var builder = new StringBuilder();
      builder.Append(assembly.EntryPoint);
      builder.Append(' ');
      builder.AppendJoin(" ", arguments);
      return builder.ToString();
    }
  }
}