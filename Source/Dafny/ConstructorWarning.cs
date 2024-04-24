using System.Linq;
using System.Reactive;
using Microsoft.Dafny;

/*
   * Code Example that displays the Warnings
   *
   * datatype Color = Red | Green | ShadesOfGray(nat)
      method MonochromaticMethod(c: Color) returns (x: bool) {
      return match c
            case Green => true
                 ^^^ Warning: Constructor name 'Green' should be followed by parentheses        
            case anythingElse => false;
        }
   */

class ConstructorWarning : IRewriter {
  internal override void PostResolve(Program program) {
    base.PostResolve(program);
    foreach (var moduleDefinition in program.Modules()) {
      foreach (var topLevelDecl in moduleDefinition.TopLevelDecls.OfType<TopLevelDeclWithMembers>()) {
        foreach (var callable in topLevelDecl.Members.OfType<ICallable>()) {
          var visitor = new ConstructorWarningVisitor(this.Reporter);
          visitor.Visit(callable, Unit.Default);
        }
      }
    }
  }
  public ConstructorWarning(ErrorReporter reporter) : base(reporter) {
  }
}
class ConstructorWarningVisitor : TopDownVisitor<Unit> {
  private readonly ErrorReporter reporter;
  public ConstructorWarningVisitor(ErrorReporter reporter) {
    this.reporter = reporter;
  }
  // Implements warning for constructors in match which ensures constructor is followed by parentheses. 
  protected override bool VisitOneExpr(Expression expr, ref Unit st) {
    if (expr is NestedMatchExpr matchExpr) {
      var matchExprCases = matchExpr.Cases;
      foreach (var caseExpr in matchExprCases) {
        CheckPattern(caseExpr.Pat);
      }
    }
    return base.VisitOneExpr(expr, ref st);
  }
  protected override bool VisitOneStmt(Statement stmt, ref Unit st) {
    if (stmt is NestedMatchStmt matchStmt) {
      foreach (var caseStmt in matchStmt.Cases) {
        CheckPattern(caseStmt.Pat);
      }
    }
    return base.VisitOneStmt(stmt, ref st);
  }
  private void CheckPattern(ExtendedPattern pattern) {
    if (pattern is not IdPattern idPattern) {
      return;
    }
    var isConstructor = idPattern.Arguments != null;
    if (isConstructor) {
      foreach (var nestedPattern in idPattern.Arguments) {
        CheckPattern(nestedPattern);
      }
      if (!idPattern.HasParenthesis) {
        this.reporter.Warning(MessageSource.Rewriter, idPattern.Tok,
          $"Constructor name '{idPattern}' should be followed by parentheses");
      }
    }
  }
}