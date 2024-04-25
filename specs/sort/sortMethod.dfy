include "./sortSpec.dfy"

module sort{

import opened sortSpec

    predicate SortSpec(input:seq<int>, output:seq<int>)
    {
        forall idx | (0 <= idx && idx < |output|-1) :: output[idx] <= output[idx+1]
    }


method merge_sort(input:seq<int>) returns (output:seq<int>)
    ensures forall idx | (0 <= idx && idx < |output|-1) :: output[idx] <= output[idx+1]
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

method merge(seqa:seq<int>, seqb:seq<int>) returns (output:seq<int>)
    requires forall idx | (0 <= idx && idx < |seqa|-1) :: seqa[idx] <= seqa[idx+1]
    requires forall idx | (0 <= idx && idx < |seqb|-1) :: seqb[idx] <= seqb[idx+1]
    // ensures SortSpec(seqa+seqb,output)
    ensures forall idx | (0 <= idx && idx < |output|-1) :: (output)[idx] <= (output)[idx+1]
    decreases |seqa|+|seqb|
    {
    var ai := 0;
    var bi := 0;
    output := [];
    while ai < |seqa| || bi < |seqb|
        invariant 0 <= ai <= |seqa|
        invariant 0 <= bi <= |seqb|
        invariant 0 < |output| && ai < |seqa| ==> output[|output|-1] <= seqa[ai]
        invariant 0 < |output| && bi < |seqb| ==> output[|output|-1] <= seqb[bi]
        invariant forall i :: 0 <= i < |output|-1 ==> output[i] <= output[i+1]
        invariant multiset(output) == multiset(seqa[..ai]) + multiset(seqb[..bi])
        invariant |output| == |seqa[..ai]| + |seqb[..bi]|; //Added
        decreases |seqa|-ai + |seqb|-bi
    {
        ghost var outputo := output;
        ghost var ao := ai;
        ghost var bo := bi;
        if ai == |seqa| || (bi < |seqb| && seqa[ai] > seqb[bi]) {
        output := output + [seqb[bi]];
        bi := bi + 1;
        // assert seqb[bo..bi] == [seqb[bo]];  // discovered by calc
        } else {
        output := output + [seqa[ai]];
        ai := ai + 1;
        // assert seqa[ao..ai] == [seqa[ao]];  // discovered by calc
        }
        assert seqa[..ai] == seqa[..ao] + seqa[ao..ai];  // discovered by calc
        assert seqb[..bi] == seqb[..bo] + seqb[bo..bi];  // discovered by calc
    }
    assert seqa == seqa[..ai];  // derived by calc
    assert seqb == seqb[..bi];
    assert |seqa+seqb| == |output|;
    return output;
    }


}