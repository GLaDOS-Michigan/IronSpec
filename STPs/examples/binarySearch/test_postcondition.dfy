include "binary_search_specs.dfy"

predicate pre_binary(intSeq:seq<int>, key:int)
{
    forall i,j | 0 <= i < j < |intSeq| :: intSeq[i] <= intSeq[j]
}

predicate post_binary(intSeq:seq<int>, key:int, r:int)
{
    && (r >= 0 ==> r < |intSeq| && intSeq[r] == key)
    && (r < 0 ==> forall i | 0 <= i < |intSeq| :: intSeq[i] != key)
}

lemma BinarySearch_original(intSeq:seq<int>, key:int) returns (r:int)
    // original
    requires pre_binary(intSeq, key)
    ensures post_binary(intSeq, key, r)
{  
    var lo:nat := 0;
    var hi:nat := |intSeq|;
    while lo < hi
    invariant 0 <= lo <= hi <= |intSeq|
    invariant forall i:nat | 0 <= i < lo :: intSeq[i] < key
    invariant forall i:nat | hi <= i < |intSeq| :: intSeq[i] > key
    {
        var mid := (lo + hi) / 2;
        if (intSeq[mid] < key) {
            lo := mid + 1;
        } else if (intSeq[mid] > key) {
            hi := mid;
        } else {
            return mid;
        }
    }
    return -1;
}
/// correctness tests - postcondition ///
/*
1. delete first line
2. delete second line
3. second line 0 < (ignore first element)
4. r < 0 || (r < |intSeq| && intSeq[r] == key)
5. second line < |intSeq| - 1 (ignore last element)
*/
lemma test_post_binary_correctness_1(intSeq:seq<int>, key:int, r:int)
     requires intSeq == [0,1,2]
    requires key in intSeq
    requires r != key
    ensures pre_binary(intSeq, key)
    ensures !post_binary(intSeq, key, r)
{
}
lemma test_post_binary_correctness_2(intSeq:seq<int>, key:int, r:int)
    requires intSeq == [1,2,2,4]
    requires key == 2
    requires r != 1 && r != 2
    ensures pre_binary(intSeq, key)
    ensures !post_binary(intSeq, key, r)
{
    assert intSeq[2] == 2;
}

lemma test_post_binary_correctness_3(intSeq:seq<int>, key:int, r:int)
    requires intSeq == []
    requires r >= 0
    ensures pre_binary(intSeq, key)
    ensures !post_binary(intSeq, key, r)
{}

lemma test_post_binary_correctness_4(intSeq:seq<int>, key:int, r:int)
    requires |intSeq| == 1
    requires key != intSeq[0] && r >= 0
    requires r >= 0
    ensures pre_binary(intSeq, key)
    ensures !post_binary(intSeq, key, r)
{}

lemma test_post_binary_correctness_5(intSeq:seq<int>, key:int, r:int)
    requires |intSeq| == 1
    requires key == intSeq[0]
    requires r != 0
    ensures pre_binary(intSeq, key)
    ensures !post_binary(intSeq, key, r)
{}

lemma test_post_binary_correctness_6(intSeq:seq<int>, key:int, r:int)
    requires intSeq == [1,2,3]
    requires key > 3
    requires r >= 0
    ensures pre_binary(intSeq, key)
    ensures !post_binary(intSeq, key, r)
{}

lemma test_post_binary_correctness_7(intSeq:seq<int>, key:int, r:int)
    requires r > |intSeq|
    ensures !post_binary(intSeq, key, r)
{}

/// provability - postcondition ///
/*
1. 0 <= r < |intSeq| && intSeq[r] == key
 */
lemma test_post_binary_provability_1(intSeq:seq<int>, key:int, r:int)
    requires intSeq == [0,1,2]
    requires key in intSeq
    requires r == key
    ensures post_binary(intSeq, key, r)
{}

lemma test_post_binary_provability_2(intSeq:seq<int>, key:int, r:int)
    requires intSeq == []
    requires r == -1
    ensures post_binary(intSeq, key, r)
{}

lemma test_post_binary_provability_3(intSeq:seq<int>, key:int, r:int)
    requires |intSeq| == 1
    requires intSeq[0] == key
    requires r == 0
    ensures post_binary(intSeq, key, r)
{}

lemma test_post_binary_provability_4(intSeq:seq<int>, key:int, r:int)
    requires |intSeq| == 1
    requires intSeq[0] != key
    requires r == -1
    ensures post_binary(intSeq, key, r)
{}

lemma test_post_binary_provability_5(intSeq:seq<int>, key:int, r:int)
    requires intSeq == [1,2,2,4]
    requires key == 2
    requires r == 1 || r == 2
    ensures post_binary(intSeq, key, r)
{}
