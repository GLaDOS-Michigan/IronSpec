﻿using System.Collections.Generic;
using System.Threading;
using Microsoft.Boogie;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public class ScopeSymbol : Symbol, ILocalizableSymbol {
    public object Node { get; }
    public readonly IToken BodyStartToken;
    public readonly IToken BodyEndToken;
    public List<ISymbol> Symbols { get; } = new();
    public override IEnumerable<ISymbol> Children => Symbols;

    public ScopeSymbol(ISymbol? scope, IRegion region) : base(scope, string.Empty) {
      Node = region;
      BodyStartToken = region.BodyStartTok;
      BodyEndToken = region.BodyEndTok;
    }

    public override TResult Accept<TResult>(ISymbolVisitor<TResult> visitor) {
      return visitor.Visit(this);
    }

    public string GetDetailText(CancellationToken cancellationToken) {
      return "";
    }
  }
}
