// RUN: %dafny /compile:3 /compileTarget:cs "%s" %S/Extern2.cs > "%t"
// RUN: %dafny /compile:3 /compileTarget:js "%s" %S/Extern3.js >> "%t"
// RUN: %dafny /compile:3 /compileTarget:go "%s" %S/Extern4.go >> "%t"
// RUN: %dafny /compile:3 /compileTarget:java "%s" %S/LibClass.java %S/OtherClass.java %S/AllDafny.java %S/Mixed.java %S/AllExtern.java >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  print "Hello\n";
  var x, y := Library.LibClass.CallMeInt(30);
  var z := Library.LibClass.CallMeNative(44, true);
  var w := Library.LibClass.CallMeInAnotherClass();
  print x, " ", y, " ", z, " ", w, "\n";

  Library.AllDafny.M();
  Library.Mixed.M();
  print Library.Mixed.F(), "\n";
  var m := new Library.Mixed();
  m.IM();
  print m.IF(), "\n";
  Library.AllExtern.P();
  assert Library.AllDafny.Seven() == Library.Mixed.Seven() == Library.AllExtern.Seven();
}

module {:extern "Library"} Library {
  newtype MyInt = x | -100 <= x < 0x8000_0000
  class {:extern "LibClass"} LibClass {
    static method {:extern} CallMeInt(x: int) returns (y: int, z: int)
    static method {:extern} CallMeNative(x: MyInt, b: bool) returns (y: MyInt)
    static method {:extern "Library.OtherClass", "CallMe"} CallMeInAnotherClass() returns (w : object)
  }

  class {:extern} AllDafny {
    static function Seven(): int { 7 }
    static method M() { print "AllDafny.M\n"; }
  }
  class {:extern} Mixed {
    constructor() { }
    static function Seven(): int { 7 }
    static method M() { print "Extern static method says: "; P(); }
    static method {:extern} P()
    method IM() { print "Extern instance method says: "; IP(); }
    method {:extern} IP()
    static function method F() : int { 1000 + G() }
    static function method {:extern} G() : int
    function method IF() : int { 2000 + IG() }
    function method {:extern} IG() : int
  }
  class {:extern} AllExtern {
    static function Seven(): int { 7 }
    static method {:extern} P()
  }
}
