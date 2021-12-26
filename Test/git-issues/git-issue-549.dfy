// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait T {
  function method bar(): bv8
}

class F extends T {
  // once upon a time, the following used to crash Dafny
  function method bar(): bv8 {
    1
  }
}

method Main() {
  var f: F := new F;
  print "bar() = ", f.bar(), "\n";
  var t: T := new F;
  print "bar() = ", t.bar(), "\n";
}
