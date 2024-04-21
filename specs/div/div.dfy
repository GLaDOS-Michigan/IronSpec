

module {:options "-functionSyntax:4"} div {

function abs(n : int) : int 
{
    if n < 0 then -n else n 
}

ghost predicate wrapper(){true}

method divRem(d :int, n:int) returns (q:int, r:int) 
    requires d >= 0
    requires n > 0 
    ensures (r + (q * n)) == d
    {

        r := d;
        var m := abs(n);
        q := 0;
        while r >= m
            invariant (r + (q * m)) == d
            invariant q >= 0
            invariant m == abs(n)
            decreases r
        {
            q := q + 1;
            r := r - m;        }
        if n < 0{
            q := -q;
        }
    }

// --- Manual hierarchy check ---

// predicate a_mut(d :int, n:int) //div
// {
//     // && d <= 0 && n > 0 //0
//     // && n >= 0 && n > 0 //1
//     // && d < 0 && n > 0 //2
//     // && d >= 0 - 1 && n > 0 //3
//     // && d != 0 && n > 0 //4
//     // && d + 1 >= 0 && n > 0 //5
//     // && d >= 0 && n < 0 //6
//     // && d >= 0 && n != 0 //7
//     // && true
// }
// predicate b_mut(d :int, n:int) //div
// {
//     // && d <= 0 && n > 0 //0
//     // && n >= 0 && n > 0 //1
//     // && d < 0 && n > 0 //2
//     // && d >= 0 - 1 && n > 0 //3
//     // && d != 0 && n > 0 //4
//     // && d + 1 >= 0 && n > 0 //5
//     // && d >= 0 && n < 0 //6
//     // && d >= 0 && n != 0 //7

//     // && d >= 0
//     // && n > 0 
//     // && true
// }

// lemma isAtLeastAsWeak(d :int, n:int)
//     requires a_mut(d,n)
//     ensures b_mut(d,n)
// {
// }

// Manually checking relative logical strength of the 8 alive mutations using lemma isAtLeastAsWeak, 
// one can easily check to see that there are 3 distinct roots in the dag of alive mutations.
// (To perform these checks, just uncomment individial lines (mutations) at a time)
// Root = 0 - (2)
// Root = 1 - (2,3,4,5)
// Root = 7 - (6)


}