// RUN: %dafny /compile:0 "%refmanexamples/Example-BV3.dfy" > "%t"
// RUN: %diff "%s.expect" "%t"
