include "./sortSpec.dfy"

module sort{

import opened sortSpec

    lemma sortWrong(input:seq<int>) returns (output:seq<int>)
        ensures SortSpecWRONG(input, output)
    {
        output := [1,4,6];
        assert SortSpecWRONG(input, output);
        return output;
    }

    // method merge_sort(input:seq<int>) returns (output:seq<int>)
    // ensures SortSpec(input, output)
    // {
    // if |input| <= 1 {
    //     output := input;
    // } else {
    //     var pivotIndex := |input| / 2;
    //     var left := input[..pivotIndex];
    //     var right := input[pivotIndex..];
    //     var leftSorted := left;
    //     leftSorted := merge_sort(left);
    //     var rightSorted := right;
    //     rightSorted := merge_sort(right);
    //     output := merge(leftSorted, rightSorted);
    //     assert left + right == input; // derived via calc

    // }
    // }

    // method merge(seqa:seq<int>, seqb:seq<int>) returns (output:seq<int>)
    // requires IsSorted(seqa)
    // requires IsSorted(seqb)
    // ensures SortSpec(seqa+seqb, output)
    // //decreases |seqa|+|seqb|
    // {
    // var ai := 0;
    // var bi := 0;
    // output := [];
    // while ai < |seqa| || bi < |seqb|
    //     invariant 0 <= ai <= |seqa|
    //     invariant 0 <= bi <= |seqb|
    //     invariant 0 < |output| && ai < |seqa| ==> output[|output|-1] <= seqa[ai]
    //     invariant 0 < |output| && bi < |seqb| ==> output[|output|-1] <= seqb[bi]
    //     invariant forall i :: 0 <= i < |output|-1 ==> output[i] <= output[i+1]
    //     invariant multiset(output) == multiset(seqa[..ai]) + multiset(seqb[..bi])
    //     decreases |seqa|-ai + |seqb|-bi
    // {
    //     ghost var outputo := output;
    //     ghost var ao := ai;
    //     ghost var bo := bi;
    //     if ai == |seqa| || (bi < |seqb| && seqa[ai] > seqb[bi]) {
    //     output := output + [seqb[bi]];
    //     bi := bi + 1;
    //     assert seqb[bo..bi] == [seqb[bo]];  // discovered by calc
    //     } else {
    //     output := output + [seqa[ai]];
    //     ai := ai + 1;
    //     assert seqa[ao..ai] == [seqa[ao]];  // discovered by calc
    //     }
    //     assert seqa[..ai] == seqa[..ao] + seqa[ao..ai];  // discovered by calc
    //     assert seqb[..bi] == seqb[..bo] + seqb[bo..bi];  // discovered by calc
    // }
    // assert seqa == seqa[..ai];  // derived by calc
    // assert seqb == seqb[..bi];
    // }

    // method fast_sort(input:seq<int>) returns (output:seq<int>)
    // //  ensures SortSpec(input, output)
    // {
    // output := [1, 2, 3];
    // }
}

/*
include "./sortSpec.dfy"

module sort{

import opened sortSpec

    // lemma sortWrong(input:seq<int>) returns (output:seq<int>)
    //     ensures SortSpecWRONG(input, output)
    // {
    //     output := [];
    //     return output;
    // }

lemma merge_sort(input:seq<int>) returns (output:seq<int>)
    ensures SortSpec(input, output)
    {
    if |input| <= 1 {
        output := input;
    } else {
        var pivotIndex := |input| / 2;
        var left := input[..pivotIndex];
        var right := input[pivotIndex..];
        var leftSorted := left;
        leftSorted := merge_sort(left);
        var rightSorted := right;
        rightSorted := merge_sort(right);
        output := merge(leftSorted, rightSorted);
        assert left + right == input; // derived via calc
        return output;

    }
    }

lemma merge(seqa:seq<int>, seqb:seq<int>) returns (output:seq<int>)
    requires IsSorted(seqa)
    requires IsSorted(seqb)
    ensures SortSpec(seqa+seqb, output)
    decreases |seqa|+|seqb|
    {
    var ai := 0;
    var bi := 0;
    output := [];
    while ai < |seqa| || bi < |seqb|
        invariant 0 <= ai <= |seqa|
        invariant 0 <= bi <= |seqb|
        // invariant 0 < |output| && ai < |seqa| ==> output[|output|-1] <= seqa[ai]
        // invariant 0 < |output| && bi < |seqb| ==> output[|output|-1] <= seqb[bi]
        invariant |output| > 0 ==> forall i :: 0 <= i < |output| ==> output[i] == 0
        invariant forall i :: 0 <= i < |output|-1 ==> output[i] <= output[i+1]
        // invariant multiset(output) == multiset(seqa[..ai]) + multiset(seqb[..bi])
        // invariant |output| == |seqa[..ai]| + |seqb[..bi]|; //Added
        
        decreases |seqa|-ai + |seqb|-bi
    {
        ghost var outputo := output;
        ghost var ao := ai;
        ghost var bo := bi;
        if ai == |seqa| || (bi < |seqb| && seqa[ai] > seqb[bi]) {
        // output := output + [seqb[bi]];
                output := output + [0];

        bi := bi + 1;
        // assert seqb[bo..bi] == [seqb[bo]];  // discovered by calc
        } else {
        // output := output + [seqa[ai]];
        output := output + [0];
        ai := ai + 1;
        // assert seqa[ao..ai] == [seqa[ao]];  // discovered by calc
        }
        assert seqa[..ai] == seqa[..ao] + seqa[ao..ai];  // discovered by calc
        assert seqb[..bi] == seqb[..bo] + seqb[bo..bi];  // discovered by calc
    }
    assert seqa == seqa[..ai];  // derived by calc
    assert seqb == seqb[..bi];
    // assert |seqa+seqb| == |output|;
    return output;
    }


}
*/