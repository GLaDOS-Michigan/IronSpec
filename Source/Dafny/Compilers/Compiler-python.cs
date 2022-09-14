using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Numerics;
using System.Text.RegularExpressions;
using JetBrains.Annotations;
using ExtensionMethods;
using Microsoft.BaseTypes;
using Microsoft.Boogie;

namespace ExtensionMethods {
  using Microsoft.Dafny;
  public static class PythonExtensions {
    public static ConcreteSyntaxTree NewBlockPy(this ConcreteSyntaxTree tree, string header = "", string footer = "",
      BlockStyle open = BlockStyle.Newline,
      BlockStyle close = BlockStyle.Nothing) {
      return tree.NewBlock(header, footer, open, close);
    }
  }
}

namespace Microsoft.Dafny.Compilers {
  public class PythonCompiler : SinglePassCompiler {
    public override IReadOnlySet<string> SupportedExtensions => new HashSet<string> { ".py" };

    public override string TargetLanguage => "Python";
    public override string TargetExtension => "py";
    public override int TargetIndentSize => 4;

    public override string TargetBaseDir(string dafnyProgramName) =>
      $"{Path.GetFileNameWithoutExtension(dafnyProgramName)}-py";

    public override bool SupportsInMemoryCompilation => false;
    public override bool TextualTargetIsExecutable => true;

    public override IReadOnlySet<string> SupportedNativeTypes =>
      new HashSet<string> { "byte", "sbyte", "ushort", "short", "uint", "int", "number", "ulong", "long" };

    private readonly List<string> Imports = new List<string> { "module_" };

    public override IReadOnlySet<Feature> UnsupportedFeatures => new HashSet<Feature> {
      Feature.Iterators,
      Feature.StaticConstants,
      Feature.IntBoundedPool,
      Feature.SequenceUpdateExpressions,
      Feature.SequenceConstructionsWithNonLambdaInitializers,
      Feature.SubsetTypeTests,
      Feature.MethodSynthesis
    };

    private const string DafnyRuntimeModule = "_dafny";
    const string DafnySetClass = $"{DafnyRuntimeModule}.Set";
    const string DafnyMultiSetClass = $"{DafnyRuntimeModule}.MultiSet";
    const string DafnySeqClass = $"{DafnyRuntimeModule}.Seq";
    const string DafnyArrayClass = $"{DafnyRuntimeModule}.Array";
    const string DafnyMapClass = $"{DafnyRuntimeModule}.Map";
    const string DafnyDefaults = $"{DafnyRuntimeModule}.defaults";
    static string FormatDefaultTypeParameterValue(TopLevelDecl tp) {
      Contract.Requires(tp is TypeParameter or OpaqueTypeDecl);
      return $"default_{tp.CompileName}";
    }
    protected override string StmtTerminator { get => ""; }
    protected override string True { get => "True"; }
    protected override string False { get => "False"; }
    protected override string Conj { get => "and"; }
    protected override void EmitHeader(Program program, ConcreteSyntaxTree wr) {
      wr.WriteLine($"# Dafny program {program.Name} compiled into Python");
      ReadRuntimeSystem(program, "DafnyRuntime.py", wr.NewFile($"{DafnyRuntimeModule}.py"));
      Imports.Add(DafnyRuntimeModule);
      EmitImports(null, wr);
      wr.WriteLine();
    }

    public override void EmitCallToMain(Method mainMethod, string baseName, ConcreteSyntaxTree wr) {
      Coverage.EmitSetup(wr);
      wr.NewBlockPy("try:")
        .WriteLine($"{mainMethod.EnclosingClass.FullCompileName}.{(IssueCreateStaticMain(mainMethod) ? "Main" : IdName(mainMethod))}()");
      wr.NewBlockPy($"except {DafnyRuntimeModule}.HaltException as e:")
        .WriteLine($"{DafnyRuntimeModule}.print(\"[Program halted] \" + {DafnyRuntimeModule}.string_of(e.message) + \"\\n\")");
    }

    protected override ConcreteSyntaxTree CreateStaticMain(IClassWriter cw) {
      return ((ClassWriter)cw).MethodWriter.NewBlockPy("def Main():");
    }

    protected override ConcreteSyntaxTree CreateModule(string moduleName, bool isDefault, bool isExtern,
        string libraryName, ConcreteSyntaxTree wr) {
      moduleName = IdProtect(moduleName);
      var file = wr.NewFile($"{moduleName}.py");
      EmitImports(moduleName, file);
      return file;
    }

    private void EmitImports(string moduleName, ConcreteSyntaxTree wr) {
      wr.WriteLine("import sys");
      wr.WriteLine("from typing import Callable, Any, TypeVar, NamedTuple");
      wr.WriteLine("from math import floor");
      wr.WriteLine("from itertools import count");
      wr.WriteLine();
      Imports.Iter(module => wr.WriteLine($"import {module}"));
      if (moduleName != null) {
        wr.WriteLine();
        wr.WriteLine($"assert \"{moduleName}\" == __name__");
        wr.WriteLine($"{moduleName} = sys.modules[__name__]");

        Imports.Add(moduleName);
      }
    }

    protected override string GetHelperModuleName() => DafnyRuntimeModule;

    private static string MangleName(string name) {
      switch (name) {
        case "False":
        case "None":
        case "True":
        case "and":
        case "as":
        case "assert":
        case "async":
        case "await":
        case "break":
        case "class":
        case "continue":
        case "def":
        case "del":
        case "elif":
        case "else":
        case "except":
        case "finally":
        case "for":
        case "from":
        case "global":
        case "if":
        case "import":
        case "in":
        case "is":
        case "lambda":
        case "nonlocal":
        case "not":
        case "or":
        case "pass":
        case "raise":
        case "return":
        case "try":
        case "while":
        case "with":
        case "yield":
          name = $"{name}_";
          break;
        default:
          while (name.StartsWith("_")) {
            name = $"{name[1..]}_";
          }
          if (name.Length > 0 && char.IsDigit(name[0])) {
            name = $"_{name}";
          }
          break;
      }
      return name;
    }

    protected override IClassWriter CreateClass(string moduleName, string name, bool isExtern, string fullPrintName,
      List<TypeParameter> typeParameters, TopLevelDecl cls, List<Type> superClasses, IToken tok, ConcreteSyntaxTree wr) {
      var realSuperClasses = superClasses?.Where(trait => !trait.IsObject).ToList() ?? new List<Type>();
      var baseClasses = realSuperClasses.Any()
        ? $"({realSuperClasses.Comma(trait => TypeName(trait, wr, tok))})"
        : "";
      var methodWriter = wr.NewBlockPy(header: $"class {IdProtect(name)}{baseClasses}:");

      var relevantTypeParameters = typeParameters.Where(NeedsTypeDescriptor);
      var args = relevantTypeParameters.Comma(tp => tp.CompileName);
      if (!string.IsNullOrEmpty(args)) { args = $", {args}"; }
      var block = methodWriter.NewBlockPy(header: $"def  __init__(self{args}):", close: BlockStyle.Newline);
      foreach (var tp in relevantTypeParameters) {
        block.WriteLine("self.{0} = {0}", tp.CompileName);
      }
      var constructorWriter = block.Fork();
      block.WriteLine("pass");

      methodWriter.NewBlockPy("def __dafnystr__(self) -> str:")
        .WriteLine($"return \"{fullPrintName}\"");
      return new ClassWriter(this, constructorWriter, methodWriter);
    }

    protected override IClassWriter CreateTrait(string name, bool isExtern, List<TypeParameter> typeParameters,
      TopLevelDecl trait, List<Type> superClasses, IToken tok, ConcreteSyntaxTree wr) {
      var methodWriter = wr.NewBlockPy(header: $"class {IdProtect(name)}:");
      // Avoids problems with member-less traits 
      if (trait is TraitDecl tr && tr.Members.All(m => m.IsGhost)) {
        methodWriter.WriteLine("pass");
      }
      return new ClassWriter(this, methodWriter, methodWriter);
    }

    protected override ConcreteSyntaxTree CreateIterator(IteratorDecl iter, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.Iterators);
    }

    protected override IClassWriter DeclareDatatype(DatatypeDecl dt, ConcreteSyntaxTree wr) {

      if (dt is TupleTypeDecl) {
        return null;
      }

      var DtT = dt.CompileName;

      var btw = wr.NewBlockPy($"class {DtT}:", close: BlockStyle.Newline);

      if (dt.HasFinitePossibleValues) {
        btw.WriteLine($"@{DafnyRuntimeModule}.classproperty");
        var w = btw.NewBlockPy(
          $"def AllSingletonConstructors(cls):");
        w.WriteLine($"return [{dt.Ctors.Select(ctor => $"{DtCtorDeclarationName(ctor, false)}()").Comma()}]");
      }

      btw.WriteLine($"@classmethod");
      var wDefault = btw.NewBlockPy($"def default(cls, {UsedTypeParameters(dt).Comma(FormatDefaultTypeParameterValue)}):");
      var arguments = dt.GetGroundingCtor().Formals.Where(f => !f.IsGhost).Comma(f => DefaultValue(f.Type, wDefault, f.tok));
      var constructorCall = $"{DtCtorDeclarationName(dt.GetGroundingCtor(), false)}({arguments})";
      if (dt is CoDatatypeDecl) {
        constructorCall = $"{dt.CompileName}__Lazy(lambda: {constructorCall})";
      }
      wDefault.WriteLine($"return lambda: {constructorCall}");

      // Ensures the inequality is based on equality defined in the constructor
      btw.NewBlockPy("def __ne__(self, __o: object) -> bool:")
        .WriteLine("return not self.__eq__(__o)");

      if (dt is CoDatatypeDecl) {
        var w = wr.NewBlockPy($"class {dt.CompileName}__Lazy({IdName(dt)}):");
        w.NewBlockPy("def __init__(self, c):")
          .WriteLine("self.c = c")
          .WriteLine("self.d = None");
        var get = w.NewBlockPy($"def _get(self):");
        get.NewBlockPy("if self.c is not None:")
          .WriteLine("self.d = self.c()")
          .WriteLine("self.c = None");
        get.WriteLine("return self.d");
        w.NewBlockPy("def __dafnystr__(self) -> str:")
          .WriteLine($"return {DafnyRuntimeModule}.string_of(self._get())");
        foreach (var destructor in from ctor in dt.Ctors
                                   let index = 0
                                   from dtor in ctor.Destructors
                                   where dtor.EnclosingCtors[0] == ctor
                                   select dtor.CorrespondingFormals[0] into arg
                                   where !arg.IsGhost
                                   select IdProtect(arg.CompileName)) {
          w.WriteLine("@property");
          w.NewBlockPy($"def {destructor}(self):")
            .WriteLine($"return self._get().{destructor}");
        }
      }

      foreach (var ctor in dt.Ctors) {
        var ctorName = IdProtect(ctor.CompileName);

        // Class-level fields don't work in all python version due to metaclasses.
        // Adding a more restrictive type would be desirable, but Python expects their definition to precede this.
        var argList = ctor.Destructors.Where(d => !d.IsGhost)
          .Select(d => $"('{IdProtect(d.CompileName)}', Any)").Comma();
        var namedtuple = $"NamedTuple('{ctorName}', [{argList}])";
        var header = $"class {DtCtorDeclarationName(ctor, false)}({DtT}, {namedtuple}):";
        var constructor = wr.NewBlockPy(header, close: BlockStyle.Newline);
        DatatypeFieldsAndConstructor(ctor, constructor);

        // @property
        // def is_Ctor0(self) -> bool:
        //   return isinstance(self, Dt_Ctor0) }
        btw.WriteLine("@property");
        btw.NewBlockPy($"def is_{ctorName}(self) -> bool:")
          .WriteLine($"return isinstance(self, {DtCtorDeclarationName(ctor)})");
      }

      return new ClassWriter(this, btw, btw);
    }

    private void DatatypeFieldsAndConstructor(DatatypeCtor ctor, ConcreteSyntaxTree wr) {
      var dt = ctor.EnclosingDatatype;

      // Dt.Ctor
      var fString = (dt.EnclosingModuleDefinition.IsDefaultModule ? "" : dt.EnclosingModuleDefinition.Name + ".") +
                dt.Name + "." + ctor.Name;

      // {self.Dtor0}, {self.Dtor1}, ..., {self.DtorN}
      var args = ctor.Formals
        .Where(f => !f.IsGhost)
        .Select(f => $"{{{DafnyRuntimeModule}.string_of(self.{IdProtect(f.CompileName)})}}")
        .Comma();

      if (args.Length > 0 && dt is not CoDatatypeDecl) {
        fString += $"({args})";
      }

      wr.NewBlockPy("def __dafnystr__(self) -> str:")
        .WriteLine($"return f\'{fString}\'");

      var argList = ctor.Formals
        .Where(f => !f.IsGhost)
        .Select(f => $"self.{IdProtect(f.CompileName)} == __o.{IdProtect(f.CompileName)}");
      var suffix = args.Length > 0 ? $" and {string.Join(" and ", argList)}" : "";

      wr.NewBlockPy("def __eq__(self, __o: object) -> bool:")
        .WriteLine($"return isinstance(__o, {DtCtorDeclarationName(ctor)}){suffix}");

      wr.NewBlockPy("def __hash__(self) -> int:")
        .WriteLine("return super().__hash__()");
    }

    private static string DtCtorDeclarationName(DatatypeCtor ctor, bool full = true) {
      var dt = ctor.EnclosingDatatype;
      return $"{(full ? dt.FullCompileName : dt.CompileName)}_{ctor.CompileName}";
    }

    protected IClassWriter DeclareType(TopLevelDecl d, SubsetTypeDecl.WKind witnessKind, Expression witness, ConcreteSyntaxTree wr) {
      var cw = (ClassWriter)CreateClass(IdProtect(d.EnclosingModuleDefinition.CompileName), IdName(d), d, wr);
      var w = cw.MethodWriter;
      var udt = UserDefinedType.FromTopLevelDecl(d.tok, d);
      w.WriteLine("@staticmethod");
      var block = w.NewBlockPy("def default():");
      var wStmts = block.Fork();
      block.Write("return ");
      if (witnessKind == SubsetTypeDecl.WKind.Compiled) {
        TrExpr(witness, block, false, wStmts);
      } else {
        block.Write(TypeInitializationValue(udt, wr, d.tok, false, false));
      }
      return cw;
    }

    protected override IClassWriter DeclareNewtype(NewtypeDecl nt, ConcreteSyntaxTree wr) {
      return DeclareType(nt, nt.WitnessKind, nt.Witness, wr);
    }

    protected override void DeclareSubsetType(SubsetTypeDecl sst, ConcreteSyntaxTree wr) {
      DeclareType(sst, sst.WitnessKind, sst.Witness, wr);
    }

    protected override void GetNativeInfo(NativeType.Selection sel, out string name, out string literalSuffix, out bool needsCastAfterArithmetic) {
      literalSuffix = "";
      needsCastAfterArithmetic = false;
      switch (sel) {
        case NativeType.Selection.Byte:
        case NativeType.Selection.SByte:
        case NativeType.Selection.UShort:
        case NativeType.Selection.Short:
        case NativeType.Selection.UInt:
        case NativeType.Selection.Int:
        case NativeType.Selection.Number:
        case NativeType.Selection.ULong:
        case NativeType.Selection.Long:
          name = "int"; break;
        default:
          Contract.Assert(false); // unexpected native type
          throw new cce.UnreachableException(); // to please the compiler
      }
    }

    protected class ClassWriter : IClassWriter {
      public readonly PythonCompiler Compiler;
      public readonly ConcreteSyntaxTree ConstructorWriter;
      public readonly ConcreteSyntaxTree MethodWriter;

      public ClassWriter(PythonCompiler compiler, ConcreteSyntaxTree constructorWriter, ConcreteSyntaxTree methodWriter) {
        Contract.Requires(compiler != null);
        Contract.Requires(methodWriter != null);
        Contract.Requires(constructorWriter != null);
        this.Compiler = compiler;
        this.ConstructorWriter = constructorWriter;
        this.MethodWriter = methodWriter;
      }

      public ConcreteSyntaxTree CreateMethod(Method m, List<TypeArgumentInstantiation> typeArgs, bool createBody,
        bool forBodyInheritance, bool lookasideBody) {
        return Compiler.CreateMethod(m, typeArgs, createBody, MethodWriter, forBodyInheritance, lookasideBody);
      }

      public ConcreteSyntaxTree SynthesizeMethod(Method m, List<TypeArgumentInstantiation> typeArgs, bool createBody, bool forBodyInheritance, bool lookasideBody) {
        throw new UnsupportedFeatureException(Token.NoToken, Feature.MethodSynthesis);
      }

      public ConcreteSyntaxTree CreateFunction(string name, List<TypeArgumentInstantiation> typeArgs,
          List<Formal> formals, Type resultType, IToken tok, bool isStatic, bool createBody, MemberDecl member,
          bool forBodyInheritance, bool lookasideBody) {
        return Compiler.CreateFunction(name, typeArgs, formals, resultType, tok, isStatic, createBody, member,
          MethodWriter, forBodyInheritance, lookasideBody);
      }

      public ConcreteSyntaxTree CreateGetter(string name, TopLevelDecl enclosingDecl, Type resultType, IToken tok,
          bool isStatic, bool isConst, bool createBody, MemberDecl member, bool forBodyInheritance) {
        return Compiler.CreateGetter(name, resultType, tok, isStatic, createBody, MethodWriter);
      }

      public ConcreteSyntaxTree CreateGetterSetter(string name, Type resultType, IToken tok, bool isStatic,
          bool createBody, MemberDecl member, out ConcreteSyntaxTree setterWriter, bool forBodyInheritance) {
        return Compiler.CreateGetterSetter(name, resultType, tok, isStatic, createBody, out setterWriter, methodWriter: MethodWriter);
      }

      public void DeclareField(string name, TopLevelDecl enclosingDecl, bool isStatic, bool isConst, Type type,
          IToken tok, string rhs, Field field) {
        Compiler.DeclareField(name, isStatic, isConst, type, tok, rhs, ConstructorWriter);
      }

      public void InitializeField(Field field, Type instantiatedFieldType, TopLevelDeclWithMembers enclosingClass) {
        throw new cce.UnreachableException();
      }

      public ConcreteSyntaxTree ErrorWriter() => MethodWriter;

      public void Finish() {

      }
    }

    private void DeclareField(string name, bool isStatic, bool isConst, Type type, IToken tok, string rhs,
        ConcreteSyntaxTree fieldWriter) {
      fieldWriter.Write($"self.{name}: {TypeName(type, fieldWriter, tok)}");
      if (rhs != null) {
        fieldWriter.Write($" = {rhs}");
      }
      fieldWriter.WriteLine();
    }

    private ConcreteSyntaxTree CreateGetterSetter(string name, Type resultType, IToken tok, bool isStatic,
      bool createBody, out ConcreteSyntaxTree setterWriter, ConcreteSyntaxTree methodWriter) {
      if (isStatic) {
        throw new UnsupportedFeatureException(Token.NoToken, Feature.StaticConstants);
      }
      methodWriter.WriteLine("@property");
      var getterWriter = methodWriter.NewBlockPy(header: $"def {name}(self):");
      methodWriter.WriteLine($"@{name}.setter");
      setterWriter = methodWriter.NewBlockPy(header: $"def {name}(self, value):");
      if (createBody) {
        return getterWriter;
      }
      getterWriter.WriteLine($"return self._{name}");
      setterWriter.WriteLine($"self._{name} = value");
      setterWriter = null;
      return null;
    }

    private ConcreteSyntaxTree CreateGetter(string name, Type resultType, IToken tok, bool isStatic, bool createBody, ConcreteSyntaxTree methodWriter) {
      if (!createBody) { return null; }
      methodWriter.WriteLine(isStatic ? $"@{DafnyRuntimeModule}.classproperty" : "@property");
      return methodWriter.NewBlockPy(header: $"def {name}({(isStatic ? "instance" : "self")}):");
    }

    private ConcreteSyntaxTree CreateMethod(Method m, List<TypeArgumentInstantiation> typeArgs, bool createBody,
        ConcreteSyntaxTree wr, bool forBodyInheritance, bool lookasideBody) {
      var customReceiver = !forBodyInheritance && NeedsCustomReceiver(m);
      if (m.IsStatic || customReceiver) { wr.WriteLine("@staticmethod"); }
      wr.Write($"def {IdName(m)}(");
      var sep = "";
      WriteFormals(m, ForTypeDescriptors(typeArgs, m, lookasideBody), m.Ins, m.IsStatic, customReceiver, ref sep, wr);
      var body = wr.NewBlockPy("):", close: BlockStyle.Newline);
      if (createBody) {
        return body;
      }
      body.WriteLine("pass");
      return null;
    }

    protected override ConcreteSyntaxTree EmitMethodReturns(Method m, ConcreteSyntaxTree wr) {
      if (m.Outs.Any(f => !f.IsGhost)) {
        var beforeReturnBlock = wr.Fork();
        EmitReturn(m.Outs, wr);
        return beforeReturnBlock;
      }
      return wr;
    }

    private void WriteFormals(MemberDecl member, List<TypeArgumentInstantiation> typeParams, List<Formal> formals, bool isStatic, bool customReceiver, ref string sep, ConcreteSyntaxTree wr) {
      if (!isStatic && !customReceiver) {
        wr.Write(sep + "self");
        sep = ", ";
      }
      WriteRuntimeTypeDescriptorsFormals(member, typeParams, wr, ref sep, FormatDefaultTypeParameterValue);
      if (customReceiver) {
        wr.Write(sep + "self");
        sep = ", ";
      }
      WriteFormals(sep, formals, wr);
    }

    private ConcreteSyntaxTree CreateFunction(string name, List<TypeArgumentInstantiation> typeArgs,
      List<Formal> formals, Type resultType, IToken tok, bool isStatic, bool createBody, MemberDecl member,
      ConcreteSyntaxTree wr, bool forBodyInheritance, bool lookasideBody) {
      if (!createBody) { return null; }
      var customReceiver = !forBodyInheritance && NeedsCustomReceiver(member);
      if (isStatic || customReceiver) { wr.WriteLine("@staticmethod"); }
      wr.Write($"def {name}(");
      var sep = "";
      WriteFormals(member, ForTypeDescriptors(typeArgs, member, lookasideBody), formals, isStatic, customReceiver, ref sep, wr);
      return wr.NewBlockPy("):", close: BlockStyle.Newline);
    }

    // Unlike the other compilers, we use lambdas to model type descriptors here.
    protected override string TypeDescriptor(Type type, ConcreteSyntaxTree wr, IToken tok) {
      Contract.Requires(type != null);
      Contract.Requires(tok != null);
      Contract.Requires(wr != null);

      return type.NormalizeExpandKeepConstraints() switch {
        var x when x.IsBuiltinArrowType => $"{DafnyDefaults}.pointer",
        // unresolved proxy; just treat as bool, since no particular type information is apparently needed for this type
        BoolType or TypeProxy => $"{DafnyDefaults}.bool",
        CharType => $"{DafnyDefaults}.char",
        IntType or BitvectorType => $"{DafnyDefaults}.int",
        RealType => $"{DafnyDefaults}.real",
        SeqType or SetType or MultiSetType or MapType => CollectionTypeDescriptor(),
        UserDefinedType udt => udt.ResolvedClass switch {
          TypeParameter tp => TypeParameterDescriptor(tp),
          ClassDecl or NonNullTypeDecl => $"{DafnyDefaults}.pointer",
          DatatypeDecl => DatatypeDescriptor(udt, udt.TypeArgs, udt.tok),
          NewtypeDecl or SubsetTypeDecl => CustomDescriptor(udt),
          _ => throw new cce.UnreachableException()
        },
        _ => throw new cce.UnreachableException()
      };

      string CollectionTypeDescriptor() {
        return TypeHelperName(type.NormalizeExpandKeepConstraints());
      }

      string TypeParameterDescriptor(TypeParameter typeParameter) {
        if (thisContext != null && typeParameter.Parent is ClassDecl and not TraitDecl) {
          return $"self.{typeParameter.CompileName}";
        }
        if (thisContext != null && thisContext.ParentFormalTypeParametersToActuals.TryGetValue(typeParameter, out var instantiatedTypeParameter)) {
          return TypeDescriptor(instantiatedTypeParameter, wr, tok);
        }
        return FormatDefaultTypeParameterValue(type.AsTypeParameter);
      }

      string CustomDescriptor(UserDefinedType userDefinedType) {
        return $"{TypeName_UDT(FullTypeName(userDefinedType), userDefinedType, wr, userDefinedType.tok)}.default";
      }

      string DatatypeDescriptor(UserDefinedType udt, List<Type> typeArgs, IToken tok) {
        var dt = (DatatypeDecl)udt.ResolvedClass;
        var w = new ConcreteSyntaxTree();
        if (dt is TupleTypeDecl) {
          w.Write($"{DafnyDefaults}.tuple(");
        } else {
          w.Write($"{TypeName_UDT(FullTypeName(udt), udt, wr, tok)}.default(");
        }
        EmitTypeDescriptorsActuals(UsedTypeParameters(dt, typeArgs), tok, w, true);
        w.Write(")");
        return w.ToString();
      }
    }

    protected override ConcreteSyntaxTree EmitTailCallStructure(MemberDecl member, ConcreteSyntaxTree wr) {
      if (!member.IsStatic && !NeedsCustomReceiver(member)) {
        wr.WriteLine("_this = self");
      }
      wr = wr.NewBlockPy($"while True:").NewBlockPy($"with {DafnyRuntimeModule}.label():");
      var body = wr.Fork();
      wr.WriteLine("break");
      return body;
    }

    protected override void EmitJumpToTailCallStart(ConcreteSyntaxTree wr) {
      wr.WriteLine($"raise {DafnyRuntimeModule}.TailCall()");
    }

    internal override string TypeName(Type type, ConcreteSyntaxTree wr, IToken tok, MemberDecl/*?*/ member = null) {
      return TypeName(type, wr, tok, boxed: false, member);
    }
    private string TypeName(Type type, ConcreteSyntaxTree wr, IToken tok, bool boxed, MemberDecl /*?*/ member = null) {
      return TypeName(type, wr, tok, boxed, false, member);
    }
    private string TypeName(Type type, ConcreteSyntaxTree wr, IToken tok, bool boxed, bool erased, MemberDecl/*?*/ member = null) {
      Contract.Ensures(Contract.Result<string>() != null);
      Contract.Assume(type != null);  // precondition; this ought to be declared as a Requires in the superclass

      var xType = type.NormalizeExpand();

      if (xType.IsObjectQ) {
        return "object";
      }

      switch (xType) {
        case BoolType:
          return "bool";
        case CharType:
          return "str";
        case IntType or BigOrdinalType or BitvectorType:
          return "int";
        case RealType:
          return $"{DafnyRuntimeModule}.BigRational";
        case UserDefinedType udt: {
            var s = FullTypeName(udt, member);
            return TypeName_UDT(s, udt, wr, udt.tok);
          }
        case CollectionType:
          return TypeHelperName(xType);
      }

      // TODO: I'm not 100% sure this is exhaustive yet
      Contract.Assert(false);
      throw new cce.UnreachableException();
    }

    protected override string TypeInitializationValue(Type type, ConcreteSyntaxTree wr, IToken tok,
        bool usePlaceboValue, bool constructTypeParameterDefaultsFromTypeDescriptors) {
      var xType = type.NormalizeExpandKeepConstraints();

      if (usePlaceboValue || xType.IsObjectQ) {
        return "None";
      }

      switch (xType) {
        case BoolType:
          return "False";
        case CharType:
          return CharType.DefaultValueAsString;
        case IntType or BigOrdinalType or BitvectorType:
          return "int(0)";
        case RealType:
          return $"{DafnyRuntimeModule}.BigRational()";
        case CollectionType:
          return $"{TypeHelperName(xType)}({{}})";
        case UserDefinedType udt: {
            var cl = udt.ResolvedClass;
            Contract.Assert(cl != null);
            switch (cl) {
              case SubsetTypeDecl td:
                switch (td.WitnessKind) {
                  case SubsetTypeDecl.WKind.Compiled:
                    return TypeName_UDT(FullTypeName(udt), udt, wr, udt.tok) + ".default()";
                  case SubsetTypeDecl.WKind.Special:
                    if (ArrowType.IsPartialArrowTypeName(td.Name)) {
                      return "None";
                    }
                    if (td is NonNullTypeDecl decl) {
                      if (decl.Class is ArrayClassDecl arr) {
                        return $"{DafnyArrayClass}.empty({arr.Dims})";
                      }
                      return "None";
                    }
                    Contract.Assert(udt.TypeArgs.Any() && ArrowType.IsTotalArrowTypeName(td.Name));
                    var rangeDefaultValue = TypeInitializationValue(udt.TypeArgs.Last(), wr, tok, usePlaceboValue,
                      constructTypeParameterDefaultsFromTypeDescriptors);
                    // The final TypeArg contains the result type
                    var arguments = udt.TypeArgs.SkipLast(1).Comma((_, i) => $"x{i}");
                    return $"(lambda {arguments}: {rangeDefaultValue})";
                  default:
                    return TypeInitializationValue(td.RhsWithArgument(udt.TypeArgs), wr, tok, usePlaceboValue,
                      constructTypeParameterDefaultsFromTypeDescriptors);
                }

              case NewtypeDecl td:
                if (td.Witness != null) {
                  return TypeName_UDT(FullTypeName(udt), udt, wr, udt.tok) + ".default()";
                } else {
                  return TypeInitializationValue(td.BaseType, wr, tok, usePlaceboValue, constructTypeParameterDefaultsFromTypeDescriptors);
                }

              case DatatypeDecl dt:
                var relevantTypeArgs = UsedTypeParameters(dt, udt.TypeArgs).ConvertAll(ta => ta.Actual);
                return dt is TupleTypeDecl
                  ? $"({relevantTypeArgs.Comma(arg => DefaultValue(arg, wr, tok, constructTypeParameterDefaultsFromTypeDescriptors))})"
                  : $"{DtCtorDeclarationName(dt.GetGroundingCtor())}.default({relevantTypeArgs.Comma(arg => TypeDescriptor(arg, wr, tok))})()";

              case TypeParameter tp:
                return constructTypeParameterDefaultsFromTypeDescriptors
                  ? $"{TypeDescriptor(udt, wr, tok)}()"
                  : $"{FormatDefaultTypeParameterValue(tp)}()";

              case ClassDecl:
                return "None";
            }
            break;
          }
      }

      Contract.Assert(false);
      throw new cce.UnreachableException();  // unexpected type
    }

    protected override string TypeName_UDT(string fullCompileName, List<TypeParameter.TPVariance> variance,
        List<Type> typeArgs, ConcreteSyntaxTree wr, IToken tok) {
      return fullCompileName;
    }

    protected override string TypeName_Companion(Type type, ConcreteSyntaxTree wr, IToken tok, MemberDecl member) {
      type = UserDefinedType.UpcastToMemberEnclosingType(type, member);
      return TypeName(type, wr, tok, member);
    }

    protected override void TypeArgDescriptorUse(bool isStatic, bool lookasideBody, TopLevelDeclWithMembers cl, out bool needsTypeParameter, out bool needsTypeDescriptor) {
      needsTypeDescriptor = false;
      needsTypeParameter = false;
      switch (cl) {
        case DatatypeDecl:
          needsTypeDescriptor = true;
          break;
        case TraitDecl:
          needsTypeDescriptor = isStatic || lookasideBody;
          break;
        case ClassDecl:
          needsTypeDescriptor = isStatic;
          break;
      }
    }

    protected override bool DeclareFormal(string prefix, string name, Type type, IToken tok, bool isInParam, ConcreteSyntaxTree wr) {
      if (isInParam) {
        wr.Write($"{prefix}{name}");
        return true;
      } else {
        return false;
      }
    }

    protected override void DeclareLocalVar(string name, Type type, IToken tok, bool leaveRoomForRhs, string rhs,
        ConcreteSyntaxTree wr) {
      wr.Write(name);
      if (type != null) { wr.Write($": {TypeName(type, wr, tok)}"); }
      if (rhs != null) { wr.Write($" = {rhs}"); }
      wr.WriteLine();
    }

    protected override ConcreteSyntaxTree DeclareLocalVar(string name, Type type, IToken tok, ConcreteSyntaxTree wr) {
      var w = new ConcreteSyntaxTree();
      wr.FormatLine($"{name} = {w}");
      return w;
    }

    protected override bool UseReturnStyleOuts(Method m, int nonGhostOutCount) => true;
    protected override bool SupportsMultipleReturns => true;

    protected override void DeclareLocalOutVar(string name, Type type, IToken tok, string rhs, bool useReturnStyleOuts,
        ConcreteSyntaxTree wr) {
      DeclareLocalVar(name, type, tok, false, rhs, wr);
    }

    protected override void EmitActualTypeArgs(List<Type> typeArgs, IToken tok, ConcreteSyntaxTree wr) {
      // emit nothing
    }

    protected override string GenerateLhsDecl(string target, Type type, ConcreteSyntaxTree wr, IToken tok) {
      return $"{target}: {TypeName(type, wr, tok)}";
    }

    protected override void EmitPrintStmt(ConcreteSyntaxTree wr, Expression arg) {
      var wStmts = wr.Fork();
      wr.Write($"{DafnyRuntimeModule}.print(");
      TrExpr(arg, wr, false, wStmts);
      wr.WriteLine(")");
    }

    protected override void EmitReturn(List<Formal> outParams, ConcreteSyntaxTree wr) {
      outParams = outParams.Where(f => !f.IsGhost).ToList();
      wr.Write("return");
      if (outParams.Count > 0) {
        wr.Write($" {outParams.Comma(IdName)}");
      }
      wr.WriteLine();
    }

    protected override ConcreteSyntaxTree CreateLabeledCode(string label, bool createContinueLabel, ConcreteSyntaxTree wr) {
      var manager = createContinueLabel ? "c_label" : "label";
      return wr.NewBlockPy($"with {DafnyRuntimeModule}.{manager}(\"{label}\"):");
    }

    protected override void EmitBreak(string label, ConcreteSyntaxTree wr) {
      wr.WriteLine(label != null ? $"raise {DafnyRuntimeModule}.Break(\"{label}\")" : "break");
    }

    protected override void EmitContinue(string label, ConcreteSyntaxTree wr) {
      wr.WriteLine($"raise {DafnyRuntimeModule}.Continue(\"{label}\")");
    }

    protected override void EmitYield(ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.Iterators);
    }

    protected override void EmitAbsurd(string message, ConcreteSyntaxTree wr) {
      if (message == null) {
        message = "unexpected control point";
      }
      wr.WriteLine($"raise Exception(\"{message}\")");
    }

    protected override void EmitHalt(IToken tok, Expression messageExpr, ConcreteSyntaxTree wr) {
      var wStmts = wr.Fork();
      wr.Write($"raise {DafnyRuntimeModule}.HaltException(");
      if (tok != null) {
        wr.Write($"{DafnyRuntimeModule}.Seq(\"{Dafny.ErrorReporter.TokenToString(tok)}: \") + ");
      }

      TrExpr(messageExpr, wr, false, wStmts);
      wr.WriteLine(")");
    }

    protected override ConcreteSyntaxTree EmitIf(out ConcreteSyntaxTree guardWriter, bool hasElse, ConcreteSyntaxTree wr) {
      wr.Write("if ");
      guardWriter = wr.Fork();
      return wr.NewBlockPy(":", hasElse ? "el" : "");
    }

    protected override ConcreteSyntaxTree EmitBlock(ConcreteSyntaxTree wr) {
      //This encoding does not provide a new scope
      return wr.NewBlockPy("if True:");
    }

    protected override ConcreteSyntaxTree EmitForStmt(IToken tok, IVariable loopIndex, bool goingUp, string endVarName,
      List<Statement> body, LList<Label> labels, ConcreteSyntaxTree wr) {
      string iterator;
      var lowWr = new ConcreteSyntaxTree();
      string argumentRemainder;
      if (endVarName == null) {
        iterator = "count";
        argumentRemainder = goingUp ? "" : "-1, -1";
      } else {
        iterator = "range";
        argumentRemainder = goingUp ? $", {endVarName}" : $"-1, {endVarName}-1, -1";
      }
      wr.Format($"for {IdName(loopIndex)} in {iterator}({lowWr}{argumentRemainder})");
      var bodyWr = wr.NewBlockPy($":");
      bodyWr = EmitContinueLabel(labels, bodyWr);
      TrStmtList(body, bodyWr);

      return lowWr;
    }

    protected override ConcreteSyntaxTree CreateWhileLoop(out ConcreteSyntaxTree guardWriter, ConcreteSyntaxTree wr) {
      wr.Write("while ");
      guardWriter = wr.Fork();
      var wBody = wr.NewBlockPy(":");
      return wBody;
    }

    protected override ConcreteSyntaxTree CreateForLoop(string indexVar, string bound, ConcreteSyntaxTree wr) {
      return wr.NewBlockPy($"for {indexVar} in range({bound}):");
    }

    protected override ConcreteSyntaxTree CreateDoublingForLoop(string indexVar, int start, ConcreteSyntaxTree wr) {
      return wr.NewBlockPy($"for {indexVar} in {DafnyRuntimeModule}.Doubler({start}):");
    }

    protected override void EmitIncrementVar(string varName, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.IntBoundedPool);
    }

    protected override void EmitDecrementVar(string varName, ConcreteSyntaxTree wr) {
      wr.WriteLine($"{varName} -= 1");
    }

    protected override string GetQuantifierName(string bvType) {
      return $"{DafnyRuntimeModule}.quantifier";
    }

    protected override ConcreteSyntaxTree CreateForeachLoop(string tmpVarName, Type collectionElementType, IToken tok,
      out ConcreteSyntaxTree collectionWriter, ConcreteSyntaxTree wr) {
      collectionWriter = new ConcreteSyntaxTree();
      wr.WriteLine($"{tmpVarName}: {TypeName(collectionElementType, wr, tok)}")
        .Format($"for {tmpVarName} in {collectionWriter}:");
      return wr.NewBlockPy();
    }

    protected override void EmitDowncastVariableAssignment(string boundVarName, Type boundVarType, string tmpVarName,
      Type collectionElementType, bool introduceBoundVar, IToken tok, ConcreteSyntaxTree wr) {
      wr.WriteLine($"{boundVarName}{(introduceBoundVar ? $": {TypeName(boundVarType, wr, tok)}" : "")} = {tmpVarName}");
    }

    protected override ConcreteSyntaxTree CreateForeachIngredientLoop(string boundVarName, int L, string tupleTypeArgs,
        out ConcreteSyntaxTree collectionWriter, ConcreteSyntaxTree wr) {
      collectionWriter = new ConcreteSyntaxTree();
      return wr.Format($"for {boundVarName} in {collectionWriter}:").NewBlockPy();
    }

    protected override void EmitNew(Type type, IToken tok, CallStmt initCall, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      var cl = ((UserDefinedType)type.NormalizeExpand()).ResolvedClass;
      var ctor = (Constructor)initCall?.Method;  // correctness of cast follows from precondition of "EmitNew"
      var sep = "";
      wr.Write($"{TypeName(type, wr, tok)}(");
      EmitTypeDescriptorsActuals(TypeArgumentInstantiation.ListFromClass(cl, type.TypeArgs), tok, wr, ref sep);
      wr.Write(ConstructorArguments(initCall, wStmts, ctor, sep));
      wr.Write(")");
    }

    protected override void EmitNewArray(Type elmtType, IToken tok, List<Expression> dimensions, bool mustInitialize,
        ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      var initValue = mustInitialize ? DefaultValue(elmtType, wr, tok, true) : "None";
      if (dimensions.Count == 1) {
        // handle the common case of 1-dimensional arrays separately
        wr.Write($"{DafnyArrayClass}([{initValue} for _ in range");
        TrParenExpr(dimensions[0], wr, false, wStmts);
        wr.Write("])");
      } else {
        wr.Write($"{DafnyRuntimeModule}.newArray({initValue}");
        foreach (var dim in dimensions) {
          wr.Write(", ");
          TrExpr(dim, wr, false, wStmts);
        }
        wr.Write(")");
      }
    }

    protected override void EmitLiteralExpr(ConcreteSyntaxTree wr, LiteralExpr e) {
      switch (e) {
        case CharLiteralExpr:
          wr.Write($"'{(string)e.Value}'");
          break;
        case StringLiteralExpr str:
          wr.Write($"{DafnyRuntimeModule}.Seq(");
          TrStringLiteral(str, wr);
          wr.Write(")");
          break;
        case StaticReceiverExpr:
          wr.Write(TypeName(e.Type, wr, e.tok));
          break;
        default:
          switch (e.Value) {
            case null:
              wr.Write("None");
              break;
            case bool value:
              wr.Write($"{value}");
              break;
            case BigInteger integer:
              wr.Write($"{integer}");
              break;
            case BigDec n:
              wr.Write($"{DafnyRuntimeModule}.BigRational('{n.Mantissa}e{n.Exponent}')");
              break;
            default:
              // TODO: This may not be exhaustive
              throw new cce.UnreachableException();
          }
          break;
      }
    }

    protected override void EmitStringLiteral(string str, bool isVerbatim, ConcreteSyntaxTree wr) {
      if (!isVerbatim) {
        wr.Write($"\"{str}\"");
      } else {
        var n = str.Length;
        wr.Write("\"");
        for (var i = 0; i < n; i++) {
          if (str[i] == '\"' && i + 1 < n && str[i + 1] == '\"') {
            wr.Write("\\\"");
            i++;
          } else if (str[i] == '\\') {
            wr.Write("\\\\");
          } else if (str[i] == '\n') {
            wr.Write("\\n");
          } else if (str[i] == '\r') {
            wr.Write("\\r");
          } else {
            wr.Write(str[i]);
          }
        }
        wr.Write("\"");
      }
    }

    protected override ConcreteSyntaxTree EmitBitvectorTruncation(BitvectorType bvType, bool surroundByUnchecked, ConcreteSyntaxTree wr) {
      var vec = wr.ForkInParens();
      wr.Write($" & ((1 << {bvType.Width}) - 1)");
      return vec;
    }

    protected override void EmitRotate(Expression e0, Expression e1, bool isRotateLeft, ConcreteSyntaxTree wr,
        bool inLetExprBody, ConcreteSyntaxTree wStmts, FCE_Arg_Translator tr) {
      // ( e0 op1 e1) | (e0 op2 (width - e1))
      EmitShift(e0, e1, isRotateLeft ? "<<" : ">>", isRotateLeft, true, wr.ForkInParens(), inLetExprBody, wStmts, tr);

      wr.Write(" | ");

      EmitShift(e0, e1, isRotateLeft ? ">>" : "<<", !isRotateLeft, false, wr.ForkInParens(), inLetExprBody, wStmts, tr);
    }

    void EmitShift(Expression e0, Expression e1, string op, bool truncate, bool firstOp, ConcreteSyntaxTree wr,
        bool inLetExprBody, ConcreteSyntaxTree wStmts, FCE_Arg_Translator tr) {
      var bv = e0.Type.AsBitVectorType;
      if (truncate) {
        wr = EmitBitvectorTruncation(bv, true, wr);
      }
      tr(e0, wr, inLetExprBody, wStmts);
      wr.Write($" {op} ");
      if (!firstOp) {
        wr = wr.ForkInParens().Write($"{bv.Width} - ");
      }

      tr(e1, wr.ForkInParens(), inLetExprBody, wStmts);
    }

    protected override void EmitEmptyTupleList(string tupleTypeArgs, ConcreteSyntaxTree wr) {
      wr.Write("[]");
    }

    protected override ConcreteSyntaxTree EmitAddTupleToList(string ingredients, string tupleTypeArgs, ConcreteSyntaxTree wr) {
      var wrTuple = new ConcreteSyntaxTree();
      wr.FormatLine($"{ingredients}.append(({wrTuple}))");
      return wrTuple;
    }

    protected override void EmitTupleSelect(string prefix, int i, ConcreteSyntaxTree wr) {
      wr.Write("{0}[{1}]", prefix, i);
    }

    protected override string IdProtect(string name) {
      return PublicIdProtect(name);
    }

    public override string PublicIdProtect(string name) {
      Contract.Requires(name != null);
      return name switch {
        _ => MangleName(name)
      };
    }

    protected override string FullTypeName(UserDefinedType udt, MemberDecl member = null) {
      if (udt is ArrowType) {
        //TODO: Add deeper types
        return "Callable";
      }

      var cl = udt.ResolvedClass;
      return cl switch {
        TypeParameter => $"TypeVar(\'{IdProtect(cl.CompileName)}\')",
        ArrayClassDecl => DafnyArrayClass,
        TupleTypeDecl => "tuple",
        _ => IdProtect(cl.FullCompileName)
      };
    }

    protected override void EmitThis(ConcreteSyntaxTree wr) {
      var isTailRecursive = enclosingMethod is { IsTailRecursive: true } || enclosingFunction is { IsTailRecursive: true };
      wr.Write(isTailRecursive ? "_this" : "self");
    }

    protected override void EmitNull(Type _, ConcreteSyntaxTree wr) {
      wr.Write("None");
    }

    protected override void EmitDatatypeValue(DatatypeValue dtv, string arguments, ConcreteSyntaxTree wr) {
      if (dtv.IsCoCall) {
        wr.Write($"{dtv.Ctor.EnclosingDatatype.FullCompileName}__Lazy(lambda: ");
        var end = wr.Fork();
        wr.Write(")");
        wr = end;
      }
      if (dtv.Ctor.EnclosingDatatype is not TupleTypeDecl) {
        wr.Write($"{DtCtorDeclarationName(dtv.Ctor)}");
      }
      wr.Write($"({arguments})");
    }

    protected override void GetSpecialFieldInfo(SpecialField.ID id, object idParam, Type receiverType,
        out string compiledName, out string preString, out string postString) {
      compiledName = "";
      preString = "";
      postString = "";
      switch (id) {
        case SpecialField.ID.UseIdParam:
          compiledName = IdProtect((string)idParam);
          break;
        case SpecialField.ID.Keys:
          compiledName = "keys";
          break;
        case SpecialField.ID.Values:
          compiledName = "values";
          break;
        case SpecialField.ID.Items:
          compiledName = "items";
          break;
        case SpecialField.ID.Floor:
          preString = "floor(";
          postString = ")";
          break;
        case SpecialField.ID.IsLimit:
          preString = $"{DafnyRuntimeModule}.BigOrdinal.is_limit(";
          postString = ")";
          break;
        case SpecialField.ID.IsSucc:
          preString = $"{DafnyRuntimeModule}.BigOrdinal.is_succ(";
          postString = ")";
          break;
        case SpecialField.ID.Offset:
          preString = $"{DafnyRuntimeModule}.BigOrdinal.offset(";
          postString = ")";
          break;
        case SpecialField.ID.IsNat:
          preString = $"{DafnyRuntimeModule}.BigOrdinal.is_nat(";
          postString = ")";
          break;
        case SpecialField.ID.ArrayLength:
        case SpecialField.ID.ArrayLengthInt:
          preString = "len(";
          postString = ")";
          if (idParam != null && (int)idParam > 0) {
            postString = string.Concat(Enumerable.Repeat("[0]", (int)idParam)) + postString;
          }
          break;
        default:
          Contract.Assert(false); // unexpected ID
          break;
      }
    }

    protected override ILvalue EmitMemberSelect(Action<ConcreteSyntaxTree> obj, Type objType, MemberDecl member,
      List<TypeArgumentInstantiation> typeArgs, Dictionary<TypeParameter, Type> typeMap, Type expectedType,
      string additionalCustomParameter = null, bool internalAccess = false) {
      switch (member) {
        case DatatypeDestructor dd: {
            var dest = dd.EnclosingClass switch {
              TupleTypeDecl => $"[{dd.Name}]",
              _ => $".{dd.CompileName}"
            };
            return SuffixLvalue(obj, dest);
          }
        case SpecialField sf: {
            GetSpecialFieldInfo(sf.SpecialId, sf.IdParam, objType, out var compiledName, out _, out _);
            return SimpleLvalue(w => {
              var customReceiver = NeedsCustomReceiver(sf) && sf.EnclosingClass is not TraitDecl;
              if (customReceiver) {
                w.Write(TypeName_Companion(objType, w, member.tok, member));
              } else {
                obj(w);
              }
              if (compiledName.Length > 0) {
                w.Write($".{(sf is ConstantField && internalAccess ? "_" : "")}{compiledName}");
              }
              var sep = "(";
              EmitTypeDescriptorsActuals(ForTypeDescriptors(typeArgs, member, false), member.tok, w, ref sep);
              if (customReceiver) {
                w.Write(sep + "self");
                sep = ", ";
              }
              if (sep != "(") {
                w.Write(")");
              }
            });
          }
        case Field: {
            return SimpleLvalue(w => {
              if (member.IsStatic) { w.Write(TypeName_Companion(objType, w, member.tok, member)); } else { obj(w); }
              w.Write($".{IdName(member)}");
            });
          }
        case Function fn: {
            if (additionalCustomParameter == null && typeArgs.Count == 0) {
              return SuffixLvalue(obj, $".{IdName(fn)}");
            }
            return SimpleLvalue(w => {
              var args = fn.Formals
                .Where(f => !f.IsGhost)
                .Select(_ => ProtectedFreshId("_eta"))
                .Comma();
              w.Write($"lambda {args}: ");
              obj(w);
              w.Write($".{IdName(fn)}(");
              var sep = "";
              EmitTypeDescriptorsActuals(ForTypeDescriptors(typeArgs, member, false), fn.tok, w, ref sep);
              if (additionalCustomParameter != null) {
                w.Write(sep + additionalCustomParameter);
                sep = ", ";
              }
              if (args.Length > 0) {
                w.Write(sep);
              }
              w.Write(args + ")");
            });
          }
        default:
          return SimpleLvalue(w => {
            w.Write($"{TypeName_Companion(objType, w, member.tok, member)}.{IdName(member)}({additionalCustomParameter ?? ""})");
          });
      }
    }

    protected override ConcreteSyntaxTree EmitArraySelect(List<string> indices, Type elmtType, ConcreteSyntaxTree wr) {
      Contract.Assert(indices != null && 1 <= indices.Count);
      var w = wr.Fork();
      foreach (var index in indices) {
        wr.Write($"[{index}]");
      }
      return w;
    }

    protected override ConcreteSyntaxTree EmitArraySelect(List<Expression> indices, Type elmtType, bool inLetExprBody,
        ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      Contract.Assert(indices != null);  // follows from precondition
      var strings = indices.Select(index => Expr(index, inLetExprBody, wStmts).ToString());
      return EmitArraySelect(strings.ToList(), elmtType, wr);
    }

    protected override void EmitExprAsInt(Expression expr, bool inLetExprBody, ConcreteSyntaxTree wr,
      ConcreteSyntaxTree wStmts) {
      // This is also used for bit shift operators, or more generally any binary operation where CompileBinOp()
      // sets the convertE1_to_int out parameter to true. This compiler always sets that to false, however,
      // so this method is only called for non-sequentializable forall statements.
      TrParenExpr("int", expr, wr, inLetExprBody, wStmts);
    }

    protected override void EmitIndexCollectionSelect(Expression source, Expression index, bool inLetExprBody,
      ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      TrParenExpr(source, wr, inLetExprBody, wStmts);
      wr.Write("[");
      TrExpr(index, wr, inLetExprBody, wStmts);
      wr.Write("]");
    }

    protected override void EmitIndexCollectionUpdate(Expression source, Expression index, Expression value,
      CollectionType resultCollectionType, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      TrParenExpr(source, wr, inLetExprBody, wStmts);
      wr.Write(".set(");
      TrExpr(index, wr, inLetExprBody, wStmts);
      wr.Write(", ");
      TrExpr(value, wr, inLetExprBody, wStmts);
      wr.Write(")");
    }

    protected override void EmitSeqSelectRange(Expression source, Expression lo, Expression hi, bool fromArray,
      bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Write($"{DafnySeqClass}(");
      TrParenExpr(source, wr, inLetExprBody, wStmts);
      wr.Write("[");
      if (lo != null) { TrExpr(lo, wr, inLetExprBody, wStmts); }
      wr.Write(":");
      if (hi != null) { TrExpr(hi, wr, inLetExprBody, wStmts); }
      wr.Write(":])");
    }

    protected override void EmitSeqConstructionExpr(SeqConstructionExpr expr, bool inLetExprBody, ConcreteSyntaxTree wr,
      ConcreteSyntaxTree wStmts) {
      ConcreteSyntaxTree valueExpression;
      string binder;
      if (expr.Initializer is LambdaExpr lam) {
        valueExpression = Expr(lam.Body, inLetExprBody, wStmts);
        binder = IdProtect(lam.BoundVars[0].CompileName);
      } else {
        throw new UnsupportedFeatureException(expr.tok, Feature.SequenceConstructionsWithNonLambdaInitializers);
      }
      wr.Write($"{DafnySeqClass}([{valueExpression} for {binder} in range({Expr(expr.N, inLetExprBody, wStmts)})])");
    }

    protected override void EmitMultiSetFormingExpr(MultiSetFormingExpr expr, bool inLetExprBody, ConcreteSyntaxTree wr,
      ConcreteSyntaxTree wStmts) {
      TrParenExpr(DafnyMultiSetClass, expr.E, wr, inLetExprBody, wStmts);
    }

    protected override void EmitApplyExpr(Type functionType, IToken tok, Expression function,
        List<Expression> arguments, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      TrExpr(function, wr, inLetExprBody, wStmts);
      TrExprList(arguments, wr, inLetExprBody, wStmts);
    }

    protected override ConcreteSyntaxTree EmitBetaRedex(List<string> boundVars, List<Expression> arguments,
      List<Type> boundTypes, Type resultType, IToken resultTok, bool inLetExprBody, ConcreteSyntaxTree wr,
      ref ConcreteSyntaxTree wStmts) {
      var functionName = ProtectedFreshId("_lambda");
      wr.Write($"{functionName}");
      TrExprList(arguments, wr, inLetExprBody, wStmts);
      var wrBody = wStmts.NewBlockPy($"def {functionName}({boundVars.Comma()}):", close: BlockStyle.Newline);
      wStmts = wrBody.Fork();
      return EmitReturnExpr(wrBody);
    }

    protected override void EmitDestructor(string source, Formal dtor, int formalNonGhostIndex, DatatypeCtor ctor,
        List<Type> typeArgs, Type bvType, ConcreteSyntaxTree wr) {
      wr.Write(source);
      wr.Write(ctor.EnclosingDatatype is TupleTypeDecl ? $"[{dtor.Name}]" : $".{IdProtect(dtor.CompileName)}");
    }

    protected override bool TargetLambdasRestrictedToExpressions => true;
    protected override ConcreteSyntaxTree CreateLambda(List<Type> inTypes, IToken tok, List<string> inNames,
        Type resultType, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts, bool untyped = false) {
      var functionName = ProtectedFreshId("_lambda");
      wr.Write($"{functionName}");
      return wStmts.NewBlockPy($"def {functionName}({inNames.Comma()}):", close: BlockStyle.Newline);
    }

    protected override void CreateIIFE(string bvName, Type bvType, IToken bvTok, Type bodyType, IToken bodyTok,
      ConcreteSyntaxTree wr, ref ConcreteSyntaxTree wStmts, out ConcreteSyntaxTree wrRhs, out ConcreteSyntaxTree wrBody) {
      wrRhs = new ConcreteSyntaxTree();
      var functionName = ProtectedFreshId("_iife");
      wr.Format($"{functionName}({wrRhs})");
      wrBody = wStmts.NewBlockPy($"def {functionName}({bvName}):");
      wStmts = wrBody.Fork();
      wrBody = EmitReturnExpr(wrBody);
    }

    protected override ConcreteSyntaxTree CreateIIFE0(Type resultType, IToken resultTok, ConcreteSyntaxTree wr,
        ConcreteSyntaxTree wStmts) {
      var functionName = ProtectedFreshId("_iife");
      wr.WriteLine($"{functionName}()");
      return wStmts.NewBlockPy($"def {functionName}():");
    }

    protected override ConcreteSyntaxTree CreateIIFE1(int source, Type resultType, IToken resultTok, string bvName,
        ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      var functionName = ProtectedFreshId("_iife");
      wr.WriteLine($"{functionName}({source})");
      return wStmts.NewBlockPy($"def {functionName}({bvName}):");
    }

    protected override void EmitUnaryExpr(ResolvedUnaryOp op, Expression expr, bool inLetExprBody,
        ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      switch (op) {
        case ResolvedUnaryOp.Cardinality:
          TrParenExpr("len", expr, wr, inLetExprBody, wStmts);
          break;
        case ResolvedUnaryOp.BitwiseNot:
          TrParenExpr("~", expr, wr, inLetExprBody, wStmts);
          break;
        case ResolvedUnaryOp.BoolNot:
          TrParenExpr("not", expr, wr, inLetExprBody, wStmts);
          break;
        default:
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected unary expression
      }
    }

    protected override void CompileBinOp(BinaryExpr.ResolvedOpcode op,
      Expression e0, Expression e1, IToken tok, Type resultType,
      out string opString,
      out string preOpString,
      out string postOpString,
      out string callString,
      out string staticCallString,
      out bool reverseArguments,
      out bool truncateResult,
      out bool convertE1_to_int,
      ConcreteSyntaxTree errorWr) {

      opString = null;
      preOpString = "";
      postOpString = "";
      callString = null;
      staticCallString = null;
      reverseArguments = false;
      truncateResult = false;
      convertE1_to_int = false;

      switch (op) {
        case BinaryExpr.ResolvedOpcode.And:
          opString = "and";
          break;

        case BinaryExpr.ResolvedOpcode.Or:
          opString = "or";
          break;

        case BinaryExpr.ResolvedOpcode.Imp:
          preOpString = "not ";
          opString = "or";
          break;

        case BinaryExpr.ResolvedOpcode.LeftShift:
          opString = "<<";
          break;

        case BinaryExpr.ResolvedOpcode.RightShift:
          opString = ">>";
          break;

        case BinaryExpr.ResolvedOpcode.Add:
        case BinaryExpr.ResolvedOpcode.Concat:
          if (resultType.IsCharType) {
            staticCallString = $"{DafnyRuntimeModule}.plus_char";
          } else {
            if (resultType.IsNumericBased() || resultType.IsBitVectorType || resultType.IsBigOrdinalType) {
              truncateResult = true;
            }
            opString = "+";
          }
          break;

        case BinaryExpr.ResolvedOpcode.Sub:
        case BinaryExpr.ResolvedOpcode.SetDifference:
        case BinaryExpr.ResolvedOpcode.MultiSetDifference:
        case BinaryExpr.ResolvedOpcode.MapSubtraction:
          if (resultType.IsCharType) {
            staticCallString = $"{DafnyRuntimeModule}.minus_char";
          } else {
            if (resultType.IsNumericBased() || resultType.IsBitVectorType || resultType.IsBigOrdinalType) {
              truncateResult = true;
            }
            opString = "-";
          }
          break;

        case BinaryExpr.ResolvedOpcode.Mul:
          opString = "*";
          truncateResult = true;
          break;

        case BinaryExpr.ResolvedOpcode.Div:
          if (resultType.IsIntegerType || resultType.IsBitVectorType || resultType.AsNewtype != null) {
            staticCallString = $"{DafnyRuntimeModule}.euclidian_division";
          } else {
            opString = "/";
          }
          break;

        case BinaryExpr.ResolvedOpcode.Mod:
          staticCallString = $"{DafnyRuntimeModule}.euclidian_modulus"; break;

        case BinaryExpr.ResolvedOpcode.ProperPrefix:
          opString = "<"; break;

        case BinaryExpr.ResolvedOpcode.Prefix:
          opString = "<="; break;

        case BinaryExpr.ResolvedOpcode.SeqEq:
        case BinaryExpr.ResolvedOpcode.SetEq:
        case BinaryExpr.ResolvedOpcode.MapEq:
        case BinaryExpr.ResolvedOpcode.EqCommon:
        case BinaryExpr.ResolvedOpcode.MultiSetEq:
          opString = "=="; break;

        case BinaryExpr.ResolvedOpcode.NeqCommon:
        case BinaryExpr.ResolvedOpcode.SeqNeq:
        case BinaryExpr.ResolvedOpcode.SetNeq:
        case BinaryExpr.ResolvedOpcode.MapNeq:
        case BinaryExpr.ResolvedOpcode.MultiSetNeq:
          opString = "!="; break;

        case BinaryExpr.ResolvedOpcode.Union:
        case BinaryExpr.ResolvedOpcode.MultiSetUnion:
        case BinaryExpr.ResolvedOpcode.MapMerge:
          opString = "|"; break;

        case BinaryExpr.ResolvedOpcode.InSet:
        case BinaryExpr.ResolvedOpcode.InMultiSet:
        case BinaryExpr.ResolvedOpcode.InSeq:
        case BinaryExpr.ResolvedOpcode.InMap:
          opString = "in"; break;

        case BinaryExpr.ResolvedOpcode.NotInSet:
        case BinaryExpr.ResolvedOpcode.NotInMultiSet:
        case BinaryExpr.ResolvedOpcode.NotInSeq:
        case BinaryExpr.ResolvedOpcode.NotInMap:
          opString = "not in"; break;

        case BinaryExpr.ResolvedOpcode.Intersection:
        case BinaryExpr.ResolvedOpcode.MultiSetIntersection:
          callString = "intersection"; break;

        case BinaryExpr.ResolvedOpcode.Disjoint:
        case BinaryExpr.ResolvedOpcode.MultiSetDisjoint:
          callString = "isdisjoint"; break;

        case BinaryExpr.ResolvedOpcode.Subset:
        case BinaryExpr.ResolvedOpcode.MultiSubset:
          callString = "issubset"; break;

        case BinaryExpr.ResolvedOpcode.ProperSubset:
        case BinaryExpr.ResolvedOpcode.ProperMultiSubset:
          callString = "ispropersubset"; break;


        default:
          base.CompileBinOp(op, e0, e1, tok, resultType,
            out opString, out preOpString, out postOpString, out callString, out staticCallString, out reverseArguments,
            out truncateResult, out convertE1_to_int,
            errorWr);
          break;
      }
    }

    protected override void TrStmtList(List<Statement> stmts, ConcreteSyntaxTree writer) {
      Contract.Requires(cce.NonNullElements(stmts));
      Contract.Requires(writer != null);
      if (stmts.Count == 0) {
        writer.WriteLine("pass");
      }
      base.TrStmtList(stmts, writer);
    }

    protected override void EmitITE(Expression guard, Expression thn, Expression els, Type resultType, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      Contract.Requires(guard != null);
      Contract.Requires(thn != null);
      Contract.Requires(thn.Type != null);
      Contract.Requires(els != null);
      Contract.Requires(resultType != null);
      Contract.Requires(wr != null);

      resultType = resultType.NormalizeExpand();
      var thenExpr = Expr(thn, inLetExprBody, wStmts);
      var castedThenExpr = resultType.Equals(thn.Type.NormalizeExpand()) ? thenExpr : Cast(resultType, thenExpr);
      var elseExpr = Expr(els, inLetExprBody, wStmts);
      var castedElseExpr = resultType.Equals(els.Type.NormalizeExpand()) ? elseExpr : Cast(resultType, elseExpr);
      wr.Format($"({castedThenExpr} if {Expr(guard, inLetExprBody, wStmts)} else {castedElseExpr})");
    }

    protected override void EmitIsZero(string varName, ConcreteSyntaxTree wr) {
      wr.Write($"{varName} == 0");
    }

    protected override void EmitConversionExpr(ConversionExpr e, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      var (pre, post) = ("", "");
      if (e.E.Type.IsNumericBased(Type.NumericPersuasion.Int) || e.E.Type.IsBitVectorType) {
        if (e.ToType.IsNumericBased(Type.NumericPersuasion.Real)) {
          (pre, post) = ($"{DafnyRuntimeModule}.BigRational(", ", 1)");
        } else if (e.ToType.IsCharType) {
          (pre, post) = ("chr(", ")");
        }
      } else if (e.E.Type.IsCharType) {
        (pre, post) = ("ord(", ")");
      } else if (e.E.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
        if (e.ToType.IsNumericBased(Type.NumericPersuasion.Int) || e.ToType.IsBitVectorType || e.ToType.IsBigOrdinalType) {
          (pre, post) = ("int(", ")");
        } else if (e.ToType.IsCharType) {
          (pre, post) = ("chr(floor(", "))");
        }
      }
      wr.Write(pre);
      TrExpr(e.E, wr, inLetExprBody, wStmts);
      wr.Write(post);
    }

    protected override void EmitTypeTest(string localName, Type fromType, Type toType, IToken tok, ConcreteSyntaxTree wr) {
      if (!fromType.IsNonNullRefType) {
        wr = wr.Write($"{localName} is {(toType.IsNonNullRefType ? "not None and" : "None or")} ").ForkInParens();
      }

      var toClass = toType.NormalizeExpand();
      wr.Write($"isinstance({localName}, {TypeName(toClass, wr, tok)})");

      var udtTo = (UserDefinedType)toType.NormalizeExpandKeepConstraints();
      if (udtTo.ResolvedClass is SubsetTypeDecl and not NonNullTypeDecl) {
        // TODO: test constraints
        throw new UnsupportedFeatureException(Token.NoToken, Feature.SubsetTypeTests);
      }
    }

    protected override void EmitCollectionDisplay(CollectionType ct, IToken tok, List<Expression> elements,
      bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      var (open, close) = ct switch {
        SeqType or MultiSetType => ("[", "]"),
        _ => ("{", "}")
      };
      wr.Write(TypeHelperName(ct));
      wr.Write("(");
      wr.Write(open);
      TrExprList(elements, wr, inLetExprBody, wStmts, parens: false);
      wr.Write(close);
      wr.Write(")");
    }

    private static string TypeHelperName(Type ct) {
      return ct switch {
        SetType => DafnySetClass,
        SeqType => DafnySeqClass,
        MapType => DafnyMapClass,
        MultiSetType => DafnyMultiSetClass,
        _ => throw new NotImplementedException()
      };
    }

    protected override void EmitMapDisplay(MapType mt, IToken tok, List<ExpressionPair> elements, bool inLetExprBody,
      ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Write($"{DafnyMapClass}({{");
      var sep = "";
      foreach (var p in elements) {
        wr.Write(sep);
        TrExpr(p.A, wr, inLetExprBody, wStmts);
        wr.Write(": ");
        TrExpr(p.B, wr, inLetExprBody, wStmts);
        sep = ", ";
      }
      wr.Write("})");
    }

    protected override void EmitSetBuilder_New(ConcreteSyntaxTree wr, SetComprehension e, string collectionName) {
      wr.WriteLine($"{collectionName} = {DafnySetClass}()");
    }

    protected override void EmitMapBuilder_New(ConcreteSyntaxTree wr, MapComprehension e, string collectionName) {
      wr.WriteLine($"{collectionName} = {DafnyMapClass}()");
    }

    protected override void EmitSetBuilder_Add(CollectionType ct, string collName, Expression elmt, bool inLetExprBody,
        ConcreteSyntaxTree wr) {
      var wStmts = wr.Fork();
      wr.WriteLine($"{collName} = {collName}.union({DafnySetClass}([{Expr(elmt, inLetExprBody, wStmts)}]))");
    }

    protected override ConcreteSyntaxTree EmitMapBuilder_Add(MapType mt, IToken tok, string collName, Expression term,
        bool inLetExprBody, ConcreteSyntaxTree wr) {
      var termLeftWriter = new ConcreteSyntaxTree();
      var wStmts = wr.Fork();
      wr.FormatLine($"{collName}[{termLeftWriter}] = {Expr(term, inLetExprBody, wStmts)}");
      return termLeftWriter;
    }

    [CanBeNull]
    protected override string GetSubtypeCondition(string tmpVarName, Type boundVarType, IToken tok, ConcreteSyntaxTree wPreconditions) {
      if (!boundVarType.IsRefType) {
        return null;
      }

      var typeTest = boundVarType.IsObject || boundVarType.IsObjectQ
        ? True
        : $"isinstance({tmpVarName}, {TypeName(boundVarType, wPreconditions, tok)})";
      return boundVarType.IsNonNullRefType
        ? $"{tmpVarName} is not None and {typeTest}"
        : $"{tmpVarName} is None or {typeTest}";
    }

    protected override string GetCollectionBuilder_Build(CollectionType ct, IToken tok, string collName, ConcreteSyntaxTree wr) {
      return TypeHelperName(ct) + $"({collName})";
    }

    protected override Type EmitIntegerRange(Type type, out ConcreteSyntaxTree wLo, out ConcreteSyntaxTree wHi, ConcreteSyntaxTree wr) {
      wr.Write($"{DafnyRuntimeModule}.IntegerRange(");
      wLo = wr.Fork();
      wr.Write(", ");
      wHi = wr.Fork();
      wr.Write(')');
      return new IntType();
    }

    protected override void EmitSingleValueGenerator(Expression e, bool inLetExprBody, string type,
      ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Write("[");
      TrExpr(e, wr, inLetExprBody, wStmts);
      wr.Write("]");
    }

    protected override void EmitHaltRecoveryStmt(Statement body, string haltMessageVarName, Statement recoveryBody, ConcreteSyntaxTree wr) {
      var tryBlock = wr.NewBlockPy("try:");
      TrStmt(body, tryBlock);
      var exceptBlock = wr.NewBlockPy($"except {DafnyRuntimeModule}.HaltException as e:");
      exceptBlock.WriteLine($"{IdProtect(haltMessageVarName)} = {DafnyRuntimeModule}.string_of(e.message)");
      TrStmt(recoveryBody, exceptBlock);
    }

    private static readonly Regex ModuleLine = new(@"^\s*assert\s+""([a-zA-Z0-9_]+)""\s*==\s*__name__\s*$");

    private static string FindModuleName(string externFilename) {
      using var rd = new StreamReader(new FileStream(externFilename, FileMode.Open, FileAccess.Read));
      while (rd.ReadLine() is { } line) {
        var match = ModuleLine.Match(line);
        if (match.Success) {
          return match.Groups[1].Value;
        }
      }
      return null;
    }

    static bool CopyExternLibraryIntoPlace(string externFilename, string mainProgram, TextWriter outputWriter) {
      // Grossly, we need to look in the file to figure out where to put it
      var moduleName = FindModuleName(externFilename);
      if (moduleName == null) {
        outputWriter.WriteLine($"Unable to determine module name: {externFilename}");
        return false;
      }
      var mainDir = Path.GetDirectoryName(mainProgram);
      Contract.Assert(mainDir != null);
      var tgtFilename = Path.Combine(mainDir, moduleName + ".py");
      var file = new FileInfo(externFilename);
      file.CopyTo(tgtFilename, true);
      if (DafnyOptions.O.CompileVerbose) {
        outputWriter.WriteLine($"Additional input {externFilename} copied to {tgtFilename}");
      }
      return true;
    }

    public override bool CompileTargetProgram(string dafnyProgramName, string targetProgramText,
        string /*?*/ callToMain, string /*?*/ targetFilename, ReadOnlyCollection<string> otherFileNames,
        bool runAfterCompile, TextWriter outputWriter, out object compilationResult) {
      compilationResult = null;
      foreach (var otherFileName in otherFileNames) {
        if (Path.GetExtension(otherFileName) != ".py") {
          outputWriter.WriteLine($"Unrecognized file as extra input for Python compilation: {otherFileName}");
          return false;
        }
        if (!CopyExternLibraryIntoPlace(otherFileName, targetFilename, outputWriter)) {
          return false;
        }
      }
      return true;
    }

    public override bool RunTargetProgram(string dafnyProgramName, string targetProgramText, string /*?*/ callToMain,
      string targetFilename, ReadOnlyCollection<string> otherFileNames, object compilationResult, TextWriter outputWriter) {
      Contract.Requires(targetFilename != null || otherFileNames.Count == 0);

      var psi = new ProcessStartInfo("python3", targetFilename) {
        CreateNoWindow = true,
        UseShellExecute = false,
        RedirectStandardInput = true,
        RedirectStandardOutput = false,
        RedirectStandardError = false,
      };

      try {
        using var pythonProcess = Process.Start(psi);
        pythonProcess.StandardInput.Close();
        pythonProcess.WaitForExit();
        return pythonProcess.ExitCode == 0;
      } catch (Exception e) {
        outputWriter.WriteLine("Error: Unable to start python ({0}): {1}", psi.FileName, e.Message);
        return false;
      }
    }
  }
}
