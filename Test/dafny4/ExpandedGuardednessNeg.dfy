// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

codatatype Stream<T> = ICons(head: T, tail: Stream<T>)

function method UpFunction(n: int): Stream<int>
{
  (k => ICons(k, UpFunction(k)))(n)  // error: this is not a co-recursive call and thus can't be proved to terminate
}

function UpFunction'(n: int): int -> Stream<int>
{
  k => ICons(k, UpFunction'(n+1)(k))  // error: the recursive function call is invoked
}
