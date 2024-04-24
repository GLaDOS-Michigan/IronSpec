module sortSpec
{


    predicate IsSorted(seqint:seq<int>)
    {
        //   forall idx :: 0 <= idx < |seqint|-1 ==> seqint[idx] <= seqint[idx+1]
// 
        forall idx | (0 <= idx && idx < |seqint|-1) :: seqint[idx] <= seqint[idx+1]
    }

    predicate SortSpec(input:seq<int>, output:seq<int>)
    {
        forall idx | (0 <= idx && idx < |input|-1) :: input[idx] <= input[idx+1]
        // && (forall idx | (0 <= idx && idx < |output|-1) :: output[idx] <= output[idx+1])
        // && |output| == |input|
        // && multiset(output) == multiset(input)
    }

    predicate SortSpecWRONG(input:seq<int>, output:seq<int>)
    {
        && IsSorted(output)
        // && multiset(output) == multiset(input)
    }

}