// RUN: %dafny /compile:0 /dprint:- "%s" /env:0 > "%t"
// RUN: %diff "%s.expect" "%t"

method Test1()
{
  var first := 0;
  var t := (ghost first:=123, 1:=234); // error
}

method Test2()
{
  var t := (1:=123, 2:=234); // error
}

method Test3()
{
  var t := (1:=123, 1:=234); // error
}
