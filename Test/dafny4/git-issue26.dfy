// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function BitvectorCast(x:bv32): int
    ensures x != 0 ==> BitvectorCast(x) != 0;
{
    x as int
}
