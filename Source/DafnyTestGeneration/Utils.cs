using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using DafnyServer.CounterexampleGeneration;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Action = System.Action;
using Errors = Microsoft.Dafny.Errors;
using Parser = Microsoft.Dafny.Parser;
using Program = Microsoft.Dafny.Program;

namespace DafnyTestGeneration {

  public static class Utils {

    /// <summary>
    /// Parse a string read (from a certain file) to a Dafny Program
    /// </summary>
    public static Program? Parse(string source, string fileName = "") {
      ModuleDecl module = new LiteralModuleDecl(new DefaultModuleDecl(), null);
      var builtIns = new BuiltIns();
      var reporter = new ConsoleErrorReporter();
      var success = Parser.Parse(source, fileName, fileName, null, module, builtIns,
        new Errors(reporter)) == 0 && Microsoft.Dafny.Main.ParseIncludes(module, builtIns,
        new List<string>(), new Errors(reporter)) == null;
      Program? program = null;
      if (success) {
        program = new Program(fileName, module, builtIns, reporter);
      }
      new Resolver(program).ResolveProgram(program);
      return program;
    }

    /// <summary>
    /// Redirect console output to capture the result of invoking an action
    /// </summary>
    public static string CaptureConsoleOutput(Action action) {

      var printer = new ConsolePrinter();
      ExecutionEngine.printer = printer;
      var originalOut = Console.Out;
      var originalErr = Console.Error;
      using var stream = new MemoryStream();
      var writer = new StreamWriter(stream);
      Console.SetOut(writer);
      Console.SetError(writer);

      action.Invoke();

      Console.Out.Flush();
      Console.Error.Flush();
      var output = Encoding.UTF8.GetString(
        stream.GetBuffer(),
        0,
        (int)stream.Length);
      Console.SetOut(originalOut);
      Console.SetError(originalErr);
      return output;
    }

    /// <summary>
    /// Restore the original name of a Dafny method from its Boogie translation
    /// </summary>
    public static string GetDafnyMethodName(string boogieName) {
      boogieName = boogieName.Split("$").Last();
      var methodName = boogieName.Split(".").Last();
      var classPath = new DafnyModelType(boogieName
        .Substring(0, boogieName.Length - methodName.Length - 1))
        .InDafnyFormat().Name
        .Split(".")
        .Where(m => m[0] != '_');
      var className = string.Join(".", classPath);
      return className.Equals("") ? methodName : $"{className}.{methodName}";
    }
  }
}