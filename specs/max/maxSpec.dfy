
module maxExample{


    predicate maxSpec(a:int,b:int,c:int) 
    {
        && (a > b ==> c == a)
        // && (a > b || c != a) 
        && (b > a ==> c == b)
        // && (c == a || c == b)
    }

}

