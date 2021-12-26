// RUN: %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:opaque} Reverse(id:int) : int

function RefineToMap(ReverseKey:int->int) : bool

function RefineToMapOfSeqNums() : bool
{
    RefineToMap(Reverse)
}
