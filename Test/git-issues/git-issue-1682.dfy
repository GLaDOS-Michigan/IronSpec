// RUN: %dafny_0 /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method IsUnique(str: array<char>) returns (ret: bool)
{
  ret := multiset
}
