﻿using IntervalTree;
using MediatR;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Util;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using AstElement = System.Object;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public class SymbolTableFactory : ISymbolTableFactory {
    private readonly ILogger logger;
    private readonly ILogger<SymbolTable> loggerSymbolTable;

    public SymbolTableFactory(ILogger<SymbolTableFactory> logger, ILogger<SymbolTable> loggerSymbolTable) {
      this.logger = logger;
      this.loggerSymbolTable = loggerSymbolTable;
    }

    public SymbolTable CreateFrom(Dafny.Program program, CompilationUnit compilationUnit, CancellationToken cancellationToken) {
      var declarations = CreateDeclarationDictionary(compilationUnit, cancellationToken);
      var designatorVisitor = new DesignatorVisitor(logger, program, declarations, compilationUnit, cancellationToken);
      var declarationLocationVisitor = new SymbolDeclarationLocationVisitor(cancellationToken);
      var symbolsResolved = !program.Reporter.HasErrorsUntilResolver;
      if (symbolsResolved) {
        designatorVisitor.Visit(program);
        declarationLocationVisitor.Visit(compilationUnit);
      } else {
        // TODO This is an unfortunate situation. The syntax could be correct but contain some semantic errors.
        //      However, due to the contracts of the resolver we cannot pro-actively check if certain information could be resolved or not.
        //      Therefore, we only have "all or nothing" when re-using the semantic model. Check if there is really no possibility to
        //      check if information was set without actually retrieving it (i.e., it's not possible to access the Type attribute due to a contract
        //      prohibiting it to be null).
        logger.LogDebug("cannot create symbol table from a program with errors");
      }
      return new SymbolTable(
        loggerSymbolTable,
        compilationUnit,
        declarations,
        declarationLocationVisitor.Locations,
        designatorVisitor.SymbolLookup,
        symbolsResolved
      );
    }

    private static IDictionary<AstElement, ILocalizableSymbol> CreateDeclarationDictionary(CompilationUnit compilationUnit, CancellationToken cancellationToken) {
      var declarations = new Dictionary<AstElement, ILocalizableSymbol>();
      foreach (var symbol in compilationUnit.GetAllDescendantsAndSelf()) {
        cancellationToken.ThrowIfCancellationRequested();
        if (symbol is ILocalizableSymbol localizableSymbol) {
          // TODO we're using try-add since it appears that nodes of the System module are re-used across several builtins.
          // TODO Maybe refine the mapping of the "declarations".
          declarations.TryAdd(localizableSymbol.Node, localizableSymbol);
        }
      }
      return declarations;
    }

    private class DesignatorVisitor : SyntaxTreeVisitor {
      private readonly ILogger logger;
      private readonly Dafny.Program program;
      private readonly IDictionary<AstElement, ILocalizableSymbol> declarations;
      private readonly DafnyLangTypeResolver typeResolver;
      private readonly IDictionary<AstElement, ISymbol> designators = new Dictionary<AstElement, ISymbol>();
      private readonly CancellationToken cancellationToken;

      private ISymbol currentScope;

      public IIntervalTree<Position, ILocalizableSymbol> SymbolLookup { get; } = new IntervalTree<Position, ILocalizableSymbol>();

      public DesignatorVisitor(
          ILogger logger, Dafny.Program program, IDictionary<AstElement, ILocalizableSymbol> declarations, ISymbol rootScope, CancellationToken cancellationToken
      ) {
        this.logger = logger;
        this.program = program;
        this.declarations = declarations;
        typeResolver = new DafnyLangTypeResolver(declarations);
        currentScope = rootScope;
        this.cancellationToken = cancellationToken;
      }

      public override void VisitUnknown(object node, IToken token) {
        logger.LogDebug("encountered unknown syntax node of type {NodeType} in {Filename}@({Line},{Column})",
          node.GetType(), token.GetDocumentFileName(), token.line, token.col);
      }

      public override void Visit(ModuleDefinition moduleDefinition) {
        cancellationToken.ThrowIfCancellationRequested();
        ProcessNestedScope(moduleDefinition, moduleDefinition.tok, () => base.Visit(moduleDefinition));
      }

      public override void Visit(ClassDecl classDeclaration) {
        VisitTopLevelDeclarationWithMembers(classDeclaration, () => base.Visit(classDeclaration));
      }

      public override void Visit(DatatypeDecl datatypeDeclaration) {
        VisitTopLevelDeclarationWithMembers(datatypeDeclaration, () => base.Visit(datatypeDeclaration));
      }

      private void VisitTopLevelDeclarationWithMembers(TopLevelDeclWithMembers declaration, System.Action visit) {
        cancellationToken.ThrowIfCancellationRequested();
        foreach (var parentTrait in declaration.ParentTraits) {
          RegisterTypeDesignator(currentScope, parentTrait);
        }
        ProcessNestedScope(declaration, declaration.tok, visit);
      }

      public override void Visit(Method method) {
        cancellationToken.ThrowIfCancellationRequested();
        ProcessNestedScope(method, method.tok, () => base.Visit(method));
      }

      public override void Visit(Function function) {
        cancellationToken.ThrowIfCancellationRequested();
        if (function.Result == null) {
          RegisterTypeDesignator(currentScope, function.ResultType);
        }
        ProcessNestedScope(function, function.tok, () => base.Visit(function));
      }

      public override void Visit(LambdaExpr lambdaExpression) {
        cancellationToken.ThrowIfCancellationRequested();
        ProcessNestedScope(lambdaExpression, lambdaExpression.tok, () => base.Visit(lambdaExpression));
      }
      public override void Visit(ForallExpr forallExpression) {
        cancellationToken.ThrowIfCancellationRequested();
        ProcessNestedScope(forallExpression, forallExpression.tok, () => base.Visit(forallExpression));
      }
      public override void Visit(ExistsExpr existsExpression) {
        cancellationToken.ThrowIfCancellationRequested();
        ProcessNestedScope(existsExpression, existsExpression.tok, () => base.Visit(existsExpression));
      }
      public override void Visit(SetComprehension setComprehension) {
        cancellationToken.ThrowIfCancellationRequested();
        ProcessNestedScope(setComprehension, setComprehension.tok, () => base.Visit(setComprehension));
      }
      public override void Visit(MapComprehension mapComprehension) {
        cancellationToken.ThrowIfCancellationRequested();
        ProcessNestedScope(mapComprehension, mapComprehension.tok, () => base.Visit(mapComprehension));
      }

      public override void Visit(LetExpr letExpression) {
        cancellationToken.ThrowIfCancellationRequested();
        ProcessNestedScope(letExpression, letExpression.tok, () => base.Visit(letExpression));
      }

      public override void Visit(Field field) {
        cancellationToken.ThrowIfCancellationRequested();
        RegisterTypeDesignator(currentScope, field.Type);
        base.Visit(field);
      }

      public override void Visit(Formal formal) {
        cancellationToken.ThrowIfCancellationRequested();
        RegisterDesignator(currentScope, formal, formal.tok, formal.Name);
        RegisterTypeDesignator(currentScope, formal.Type);
        base.Visit(formal);
      }

      public override void Visit(NonglobalVariable variable) {
        cancellationToken.ThrowIfCancellationRequested();
        RegisterDesignator(currentScope, variable, variable.tok, variable.Name);
        RegisterTypeDesignator(currentScope, variable.Type);
        base.Visit(variable);
      }

      public override void Visit(BlockStmt blockStatement) {
        cancellationToken.ThrowIfCancellationRequested();
        ProcessNestedScope(blockStatement, blockStatement.Tok, () => base.Visit(blockStatement));
      }

      public override void Visit(ExprDotName expressionDotName) {
        cancellationToken.ThrowIfCancellationRequested();
        base.Visit(expressionDotName);
        if (typeResolver.TryGetTypeSymbol(expressionDotName.Lhs, out var leftHandSideType)) {
          RegisterDesignator(leftHandSideType, expressionDotName, expressionDotName.tok, expressionDotName.SuffixName);
        }
      }

      public override void Visit(NameSegment nameSegment) {
        cancellationToken.ThrowIfCancellationRequested();
        RegisterDesignator(currentScope, nameSegment, nameSegment.tok, nameSegment.Name);
      }

      public override void Visit(TypeRhs typeRhs) {
        cancellationToken.ThrowIfCancellationRequested();
        RegisterTypeDesignator(currentScope, typeRhs.EType);
        base.Visit(typeRhs);
      }

      public override void Visit(FrameExpression frameExpression) {
        cancellationToken.ThrowIfCancellationRequested();
        RegisterDesignator(currentScope, frameExpression, frameExpression.tok, frameExpression.FieldName);
      }

      public override void Visit(IdentifierExpr identifierExpression) {
        cancellationToken.ThrowIfCancellationRequested();
        RegisterDesignator(currentScope, identifierExpression, identifierExpression.tok, identifierExpression.Name);
        base.Visit(identifierExpression);
      }

      public override void Visit(LocalVariable localVariable) {
        cancellationToken.ThrowIfCancellationRequested();
        // TODO The type of a local variable may be visited twice when its initialized at declaration.
        //      It is visited first for the declaration itself and then for the update (initialization).
        // RegisterTypeDesignator(_currentScope, localVariable.Type);
        base.Visit(localVariable);
      }

      private void RegisterTypeDesignator(ISymbol scope, Type type) {
        // TODO We currently rely on the resolver to locate "NamePath" (i.e. the type designator).
        //      The "typeRhs" only points to the "new" keyword with its token.
        //      Find an alternative to get the type designator without requiring the resolver.
        if (type is UserDefinedType userDefinedType) {
          RegisterDesignator(scope, type, userDefinedType.NamePath.tok, userDefinedType.Name);
        }
      }

      private void RegisterDesignator(ISymbol scope, AstElement node, Boogie.IToken token, string identifier) {
        var symbol = GetSymbolDeclarationByName(scope, identifier);
        if (symbol != null) {
          // Many resolutions for automatically generated nodes (e.g. Decreases, Update when initializating a variable
          // at declaration) cause duplicated visits. These cannot be prevented at this time as it seems there's no way
          // to distinguish nodes from automatically created one (i.e. nodes of the original syntax tree vs. nodes of the
          // abstract syntax tree). We just ignore such duplicates until more information is availabe in the AST.
          var range = token.GetLspRange();
          SymbolLookup.Add(range.Start, range.End, symbol);
          if (designators.TryGetValue(node, out var registeredSymbol)) {
            if (registeredSymbol != symbol) {
              logger.LogInformation("Conflicting symbol resolution of designator named {Identifier} in {Filename}@({Line},{Column})",
                identifier, token.GetDocumentFileName(), token.line, token.col);
            }
          } else {
            designators.Add(node, symbol);
          }
        } else {
          logger.LogInformation("could not resolve the symbol of designator named {Identifier} in {Filename}@({Line},{Column})",
            identifier, token.GetDocumentFileName(), token.line, token.col);
        }
      }

      private void ProcessNestedScope(AstElement node, Boogie.IToken token, System.Action visit) {
        if (!program.IsPartOfEntryDocument(token)) {
          return;
        }
        var oldScope = currentScope;
        currentScope = declarations[node];
        visit();
        currentScope = oldScope;
      }

      private ILocalizableSymbol? GetSymbolDeclarationByName(ISymbol scope, string name) {
        var currentScope = scope;
        while (currentScope != null) {
          foreach (var child in currentScope.Children.OfType<ILocalizableSymbol>()) {
            cancellationToken.ThrowIfCancellationRequested();
            if (child.Name == name) {
              return child;
            }
          }
          currentScope = currentScope.Scope;
        }
        return null;
      }
    }

    private class SymbolDeclarationLocationVisitor : ISymbolVisitor<Unit> {
      private readonly CancellationToken cancellationToken;

      public IDictionary<ISymbol, SymbolLocation> Locations { get; } = new Dictionary<ISymbol, SymbolLocation>();

      public SymbolDeclarationLocationVisitor(CancellationToken cancellationToken) {
        this.cancellationToken = cancellationToken;
      }

      public Unit Visit(ISymbol symbol) {
        symbol.Accept(this);
        return Unit.Value;
      }

      public Unit Visit(CompilationUnit compilationUnit) {
        VisitChildren(compilationUnit);
        return Unit.Value;
      }

      public Unit Visit(ModuleSymbol moduleSymbol) {
        cancellationToken.ThrowIfCancellationRequested();
        RegisterLocation(
          moduleSymbol,
          moduleSymbol.Declaration.tok,
          moduleSymbol.Declaration.tok.GetLspRange(),
          new Range(moduleSymbol.Declaration.tok.GetLspPosition(), moduleSymbol.Declaration.BodyEndTok.GetLspPosition())
        );
        VisitChildren(moduleSymbol);
        return Unit.Value;
      }

      public Unit Visit(ClassSymbol classSymbol) {
        return VisitTypeSymbol(classSymbol);
      }

      public Unit Visit(DataTypeSymbol datatypeSymbol) {
        return VisitTypeSymbol(datatypeSymbol);
      }

      private Unit VisitTypeSymbol<TNode>(TypeWithMembersSymbolBase<TNode> typeSymbol) where TNode : TopLevelDeclWithMembers {
        cancellationToken.ThrowIfCancellationRequested();
        RegisterLocation(
          typeSymbol,
          typeSymbol.Declaration.tok,
          typeSymbol.Declaration.tok.GetLspRange(),
          new Range(typeSymbol.Declaration.tok.GetLspPosition(), typeSymbol.Declaration.BodyEndTok.GetLspPosition())
        );
        VisitChildren(typeSymbol);
        return Unit.Value;
      }

      public Unit Visit(ValueTypeSymbol valueTypeSymbol) {
        cancellationToken.ThrowIfCancellationRequested();
        RegisterLocation(
          valueTypeSymbol,
          valueTypeSymbol.Declaration.tok,
          valueTypeSymbol.Declaration.tok.GetLspRange(),
          new Range(valueTypeSymbol.Declaration.tok.GetLspPosition(), valueTypeSymbol.Declaration.BodyEndTok.GetLspPosition())
        );
        VisitChildren(valueTypeSymbol);
        return Unit.Value;
      }

      public Unit Visit(FieldSymbol fieldSymbol) {
        cancellationToken.ThrowIfCancellationRequested();
        RegisterLocation(
          fieldSymbol,
          fieldSymbol.Declaration.tok,
          fieldSymbol.Declaration.tok.GetLspRange(),
          // BodyEndToken always returns Token.NoToken
          fieldSymbol.Declaration.tok.GetLspRange()
        );
        VisitChildren(fieldSymbol);
        return Unit.Value;
      }

      public Unit Visit(FunctionSymbol functionSymbol) {
        cancellationToken.ThrowIfCancellationRequested();
        RegisterLocation(
          functionSymbol,
          functionSymbol.Declaration.tok,
          functionSymbol.Declaration.tok.GetLspRange(),
          GetDeclarationRange(functionSymbol.Declaration)
        );
        VisitChildren(functionSymbol);
        return Unit.Value;
      }

      public Unit Visit(MethodSymbol methodSymbol) {
        cancellationToken.ThrowIfCancellationRequested();
        RegisterLocation(
          methodSymbol,
          methodSymbol.Declaration.tok,
          methodSymbol.Declaration.tok.GetLspRange(),
          GetDeclarationRange(methodSymbol.Declaration)
        );
        VisitChildren(methodSymbol);
        return Unit.Value;
      }

      private static Range GetDeclarationRange(Declaration declaration) {
        return declaration.BodyEndTok == Token.NoToken
          ? declaration.tok.GetLspRange()
          : new Range(declaration.tok.GetLspPosition(), declaration.BodyEndTok.GetLspPosition());
      }

      public Unit Visit(VariableSymbol variableSymbol) {
        cancellationToken.ThrowIfCancellationRequested();
        RegisterLocation(
          variableSymbol,
          variableSymbol.Declaration.Tok,
          variableSymbol.Declaration.Tok.GetLspRange(),
          variableSymbol.Declaration.Tok.GetLspRange()
        );
        VisitChildren(variableSymbol);
        return Unit.Value;
      }

      public Unit Visit(ScopeSymbol scopeSymbol) {
        cancellationToken.ThrowIfCancellationRequested();
        var endToken = scopeSymbol.BodyEndToken;
        RegisterLocation(
          scopeSymbol,
          scopeSymbol.BodyStartToken,
          scopeSymbol.BodyStartToken.GetLspRange(),
          new Range(scopeSymbol.BodyStartToken.GetLspPosition(), endToken.GetLspPosition())
        );
        VisitChildren(scopeSymbol);
        return Unit.Value;
      }

      private void VisitChildren(ISymbol symbol) {
        foreach (var child in symbol.Children) {
          child.Accept(this);
        }
      }

      private void RegisterLocation(ISymbol symbol, IToken token, Range name, Range declaration) {
        if (token.Filename != null) {
          // The filename is null if we have a default or System based symbol. This is also reflected by the ranges being usually -1.
          Locations.Add(symbol, new SymbolLocation(token.GetDocumentUri(), name, declaration));
        }
      }
    }
  }
}
