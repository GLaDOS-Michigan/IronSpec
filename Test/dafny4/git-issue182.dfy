// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate method prop()
ensures prop; // OOPS! Forgot () after prop
{
true
}
