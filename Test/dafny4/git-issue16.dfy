// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "git-issue16.dfyi"

lemma UhOh()
  ensures false
{
}
