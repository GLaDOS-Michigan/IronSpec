

module {:options "-functionSyntax:4"} nHarm {


ghost predicate wrapper(){true}

method NthHarmonic(x:int) returns (c:int)
    requires x >= 1
{
    if x < 0 {
        return 1/0;
    }
    return 1/(x+1);
}

// method HarmonicSum(n:int) returns (r:int)
//     requires n >= 0
//     {
//         var n0 := NthHarmonic(n);
//         var n1 := NthHarmonic(n+1);
//         r := n0 + n1;
//     }




///////harmonic

// // Mutation that Passes = 0
// // 	 mutation: requires x + 1 >= 1
// // 	 orig: requires x >= 1

// // Mutation that Passes = 1
// // 	 mutation: requires x >= 1 - 1
// // 	 orig: requires x >= 1



// predicate a_mut(x :int) //harmonic
// {
//             // x + 1 >= 1 // 0
//             x >= 1 - 1 // 1
// }

// predicate b_mut(x :int) //harmonic
// {
//             x + 1 >= 1 // 0
//             // x >= 1 - 1 // 1
// }

// lemma isAtLeastAsWeak(x:int)
//     requires a_mut(x)
//     ensures b_mut(x)
// {
// }



// Manually checking relative logical strength of the 2 alive mutations using lemma isAtLeastAsWeak, 
// one can easily check to see that there are 2 distinct roots in the dag of alive mutations.
// (To perform these checks, just uncomment individial lines (mutations) at a time)
// Root = 0 - ()
// Root = 1 - ()


}