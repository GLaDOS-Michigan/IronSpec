// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Examples from https://www.haskell.org/tutorial/functions.html

method Main()
{
  var n := 7;
  Print(n, "ones()", ones());
  Print(n, "from(3)", from(3));
  Print(n, "Map(plus1, ones())", Map(plus1, ones()));
  Print(n, "Map(plus1, from(3))", Map(plus1, from(3)));
  Print(n, "squares()", squares());
  PrintList("take(5, from(3))", take(5, from(3)));
  Print(n, "zip(ones(), from(3)", zip(ones(), from(3)));
  Print(n, "addPair(zip(ones(), from(3))", addPair(zip(ones(), from(3))));
  Print(n, "fib()", fib());
  Print(n, "add(ones(), from(3))", add(ones(), from(3)));
  Print(n, "Fib()", Fib());
  Print(n, "Fib0()", Fib0());
  Print(n, "Fib1()", Fib1());
  Print(n, "OhOnes()", OhOnes());
  Print(n, "Combine(plus, ones(), from(3))", Combine(plus, ones(), from(3)));
}

method Print<T>(n: nat, msg: string, s: Stream<T>) {
  print msg, ": ";
  var i, s := 0, s;
  while i < n {
    print s.head, " ";
    i, s := i + 1, s.tail;
  }
  print "...\n";
}

method PrintList<T>(msg: string, s: List<T>) {
  print msg, ": ";
  var s := s;
  while s != Nil
    decreases s
  {
    print s.head, " ";
    s := s.tail;
  }
  print "\n";
}

function method plus1(x: int): int { x + 1 }
function method plus(x: int, y: int): int { x + y }

datatype List<T> = Nil | ListCons(head: T, tail: List<T>)
codatatype Stream<T> = Cons(head: T, tail: Stream<T>)

function method ones(): Stream<int>
{
  Cons(1, ones())
}

function method from(n: int): Stream<int>
{
  Cons(n, from(n+1))
}

function method Map<T,U>(f: T -> U, s: Stream<T>): Stream<U>
{
  Cons(f(s.head), Map(f, s.tail))
}

function method squares(): Stream<int>
{
  Map(x => x*x, from(0))
}

function method take(n: nat, s: Stream): List
{
  if n == 0 then Nil else ListCons(s.head, take(n-1, s.tail))
}

function method {:abstemious} zip<T,U>(a: Stream<T>, b: Stream<U>): Stream<(T,U)>
{
  Cons((a.head, b.head), zip(a.tail, b.tail))
}

function method {:abstemious} addPair(a: Stream<(int,int)>): Stream<int>
{
  Cons(a.head.0 + a.head.1, addPair(a.tail))
}

function method fib(): Stream<int>
{
  Cons(0, Cons(1, addPair(zip(fib(), fib().tail))))
}

function method {:abstemious} add(a: Stream<int>, b: Stream<int>): Stream<int>
{
  Cons(a.head + b.head, add(a.tail, b.tail))
}

function method Fib(): Stream<int>
{
  Cons(0, Cons(1, add(Fib(), Fib().tail)))
}

function method Fib0(): Stream<int>
{
  Cons(0, Fib1())
}

function method Fib1(): Stream<int>
{
  Cons(1, add(Fib0(), Fib1()))
}

function method OhOnes(): Stream<int>
{
  Cons(0, Cons(1, OhOnes().tail))
}

function method {:abstemious}
  Combine<T>(f: (T,T) -> T, a: Stream, b: Stream): Stream
{
  Cons(f(a.head, b.head), Combine(f, a.tail, b.tail))
}

// ---- various fun lemmas ----

function nth<T>(n: nat, s: Stream<T>): T
{
  if n == 0 then s.head else nth(n-1, s.tail)
}

function nfib(n: nat): nat
{
  if n < 2 then n else nfib(n-2) + nfib(n-1)
}

lemma Ones_Correct(n: nat)
  ensures nth(n, ones()) == 1
{
}

greatest lemma OhOnesTail_Correct()
  ensures OhOnes().tail == ones()
{
}

greatest lemma OhOnes_Correct()
  ensures OhOnes() == Cons(0, ones())
{
}

lemma OhOnes_Correct'(n: nat)
  ensures nth(n, OhOnes()) == if n == 0 then 0 else 1
{
  OhOnes_Correct();
  if n != 0 {
    Ones_Correct(n-1);
  }
}

lemma C_Correct(n: nat, k: int)
  ensures nth(n, Combine(plus, ones(), from(k))) == k + 1 + n
{
}

greatest lemma CombinePlus_Correct(a: Stream<int>, b: Stream<int>)
  ensures Combine(plus, a, b) == add(a, b)
{
}

lemma add_Correct(n: nat, a: Stream<int>, b: Stream<int>)
  ensures nth(n, add(a, b)) == nth(n, a) + nth(n, b)
{
}

function StraightFibonacci(n: nat): Stream<int>
{
  Cons(nfib(n), StraightFibonacci(n+1))
}

lemma StraightFibonacci_Correct(n: nat, k: nat)
  ensures nth(n, StraightFibonacci(k)) == nfib(k + n)
{
}

lemma Fib_Correct(n: nat)
  ensures nth(n, Fib()) == nfib(n)
{
  if n < 2 {
  } else {
    var F  := Fib();
    calc {
      nth(n, F);
    ==
      nth(n-2, F.tail.tail);
    ==
      nth(n-2, add(Fib(), Fib().tail));
    ==  { add_Correct(n-2, Fib(), Fib().tail); }
      nth(n-2, Fib()) + nth(n-2, Fib().tail);
    ==
      nth(n-2, Fib()) + nth(n-1, Fib());
    ==  { Fib_Correct(n-2); Fib_Correct(n-1); }
      nfib(n-2) + nfib(n-1);
    ==
      nfib(n);
    }
  }
}
