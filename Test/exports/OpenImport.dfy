// RUN: %dafny /env:0 /dprint:"%t.dfy" /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A{
  export provides T
  export Spec provides f,T

  type T = int
  function f(): T { 0 }

}

module B {
  import opened A`Spec

  export Body provides A reveals g,h
  function g(): T { f() }
  function h(): A.T { f() }
}

module BBad {
  import opened A`Spec

  export Body reveals g,h // we need A
  function g(): T { f() }
  function h(): A.T { f() }
}

module C {
  import opened B`Body
  import AA = A //imports must be qualified, here A refers to the default export of the module A

  function h(): AA.T { AA.f() } // error, AA is A's default export, which does not give f
  function i(): A.T { A.f() } // qualification is fine
  function j(): A.T { f() } // not okay, we don't import openness

}
