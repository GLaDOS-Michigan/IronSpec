// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Atom = MakeAtom(value: int)

method Test() {
  var r: Atom;
  r := MakeAtom;  // this is an error, because the use of MakeAtom requires a parameter
}

