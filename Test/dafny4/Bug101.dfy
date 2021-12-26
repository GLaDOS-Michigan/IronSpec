// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate P(i:int) { true }

lemma Tester()
{
//    forall i ensures false ==> P(i) {}
    forall i ensures P(i) <== false {}
    assert forall i :: P(i) ==> false;
    assert P(0);
    assert false;
}






