// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

trait Trait<Y> {
  const y: Y
  const k: Y := y
  const l: Y
}

class ClassB extends Trait<array<bv8>> {
  var m: array<bv8>
  constructor () { m := new bv8[42]; }
}

class ClassC extends Trait<array3<bv8>> {
  var m: array3<bv8>
  constructor () { m := new bv8[8, 9, 10]; }
}

method Main() {
  var cb := new ClassB();
  print cb.y.Length, " ", cb.k.Length, " ", cb.l.Length, " ", cb.m.Length, "\n";
  var cc := new ClassC();
  print cc.y.Length1, " ", cc.k.Length1, " ", cc.l.Length1, " ", cc.m.Length1, "\n";
}

