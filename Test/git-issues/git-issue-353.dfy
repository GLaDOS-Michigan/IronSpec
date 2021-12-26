// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type A = s : seq<int> | |s| < 10

method f(a: seq<A>)
  ensures multiset(a[..]) == multiset(a[..])
{
}
