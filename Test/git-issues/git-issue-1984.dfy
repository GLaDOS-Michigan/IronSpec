// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method {:extern "test"} testInt(i: int)
method {:extern "test"} testBool(b: bool) // Previously the verifier reported a name collision
