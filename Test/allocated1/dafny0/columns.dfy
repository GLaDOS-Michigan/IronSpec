// RUN: %dafny /verifyAllModules /allocated:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
include "../../dafny0/columns.dfy"
