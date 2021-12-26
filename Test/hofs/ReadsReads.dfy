// RUN: %dafny /print:"%t.print" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module ReadsRequiresReads {
  function MyReadsOk<A,B>(f : A ~> B, a : A) : set<object?>
    reads f.reads(a)
  {
    f.reads(a)
  }

  function MyReadsOk2<A,B>(f : A ~> B, a : A) : set<object?>
    reads f.reads(a)
  {
    (f.reads)(a)
  }

  function MyReadsOk3<A,B>(f : A ~> B, a : A) : set<object?>
    reads (f.reads)(a)
  {
    f.reads(a)
  }

  function MyReadsOk4<A,B>(f : A ~> B, a : A) : set<object?>
    reads (f.reads)(a)
  {
    (f.reads)(a)
  }

  function MyReadsBad<A,B>(f : A ~> B, a : A) : set<object?>
  {
    f.reads(a)  // error: MyReadsBad does not have permission to read what f.reads(a) reads
  }

  function MyReadsBad2<A,B>(f : A ~> B, a : A) : set<object?>
  {
    (f.reads)(a)  // error: MyReadsBad2 does not have permission to read what f.reads(a) reads
  }

  function MyReadsOk'<A,B>(f : A ~> B, a : A, o : object) : bool
    reads f.reads(a)
  {
    o in f.reads(a)
  }

  function MyReadsBad'<A,B>(f : A ~> B, a : A, o : object) : bool
  {
    o in f.reads(a)  // error: MyReadsBad' does not have permission to read what f.reads(a) reads
  }

  function MyRequiresOk<A,B>(f : A ~> B, a : A) : bool
    reads f.reads(a)
  {
    f.requires(a)
  }

  function MyRequiresBad<A,B>(f : A ~> B, a : A) : bool
  {
    f.requires(a)  // error: MyRequiresBad does not have permission to read what f.requires(a) reads
  }
}

module WhatWeKnowAboutReads {
  function ReadsNothing():(){()}

  lemma IndeedNothing() {
    assert ReadsNothing.reads() == {};
    assert ((ReadsNothing).reads)() == {};
  }

  method NothingHere() {
    assert (() => ()).reads() == {};
  }

  class S {
    var s : S?
  }

  function ReadsSomething(s : S?):()
    reads s
  {()}

  method MaybeSomething() {
    var s  := new S;
    var s' := new S;
           if * { assert s in ReadsSomething.reads(s) || ReadsSomething.reads(s) == {};
    } else if * { assert s in ReadsSomething.reads(s);
    } else if * { assert ReadsSomething.reads(s) == {};  // error
    } else if * { assert s' !in ReadsSomething.reads(s);
    } else if * { assert s' in ReadsSomething.reads(s);  // error
    }
  }

  method SomethingHere() {
    var s  := new S;
    var s' := new S;
    var f := (u) reads u => ();
           if * { assert s in f.reads(s) || f.reads(s) == {};
    } else if * { assert s in f.reads(s);
    } else if * { assert f.reads(s) == {};  // error
    } else if * { assert s' !in f.reads(s);
    } else if * { assert s' in f.reads(s);  // error
    }
  }
}

module ReadsAll {
  function A(f: int ~> int) : int
    reads set x,o | o in f.reads(x) :: o  // note, with "set o,x ..." instead, Dafny complains (this is perhaps less than ideal)
    requires forall x :: f.requires(x)
  {
    f(0) + f(1) + f(2)
  }

  function method B(f: int ~> int) : int
    reads set x,o | o in f.reads(x) :: o  // note, with "set o,x ..." instead, Dafny complains (this is perhaps less than ideal)
    requires forall x :: f.requires(x)
  {
    f(0) + f(1) + f(2)
  }

  function C(f: int ~> int) : int
    reads f.reads
    requires forall x :: f.requires(x)
  {
    f(0) + f(1) + f(2)
  }

  function method D(f: int ~> int) : int
    reads f.reads
    requires forall x :: f.requires(x)
  {
    f(0) + f(1) + f(2)
  }
}

module ReadsOnFunctions {
  lemma Requires_Reads_What_Function_Reads(f: int ~> int)
  {
    var g := f.requires;
    assert g.reads(10) == f.reads(10);
  }
}
