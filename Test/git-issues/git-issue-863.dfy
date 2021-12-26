// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype D = D(ghost v:nat)
function method p():D { ghost var v:nat :| true; D(v) }

datatype G = G(v:nat)
function method q():G { var v:nat :| true; G(v) }

