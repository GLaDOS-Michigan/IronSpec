// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype DT<T(0)> = Make | Create {
  static const b := 30
  static const t: T
}

method Test1() {
  var t := DT<int>.t;  // this work
  var u := DT.t;  // this gives an "underspecified type" error, as expected
}

