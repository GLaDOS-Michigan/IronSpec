include "binary_search_specs.dfy"

predicate pre_binary(intSeq:seq<int>, key:int)
{
    forall i,j | 0 <= i < j < |intSeq| :: intSeq[i] <= intSeq[j]
}

predicate post_binary(intSeq:seq<int>, key:int, r:int)
{
    && (r >= 0 ==> r < |intSeq| && intSeq[r] == key)
    && (r < 0 ==> forall i:nat | i < |intSeq| :: intSeq[i] != key)
}

/// usefulness tests ///
/*
1. forall elements intSeq[i] < intSeq[j]
*/
lemma test_pre_binary_usefulness_1(intSeq:seq<int>, key:int)
    requires intSeq == []
    ensures pre_binary(intSeq, key)
{}

lemma test_pre_binary_usefulness_2(intSeq:seq<int>, key:int)
    requires |intSeq| == 1
    ensures pre_binary(intSeq, key)
{}

lemma test_pre_binary_usefulness_3(intSeq:seq<int>, key:int)
    requires intSeq == [1,2]
    ensures pre_binary(intSeq, key)
{}

lemma test_pre_binary_usefulness_4(intSeq:seq<int>, key:int)
    requires intSeq == [-1,-1]
    ensures pre_binary(intSeq, key)
{}

lemma test_pre_binary_usefulness_5(intSeq:seq<int>, key:int)
    requires intSeq == [1,2,3]
    ensures pre_binary(intSeq, key)
{}

lemma test_pre_binary_usefulness_6(intSeq:seq<int>, key:int)
    requires intSeq == [1,1,2,2,2,3]
    ensures pre_binary(intSeq, key)
{}

lemma test_pre_binary_usefulness_7(intSeq:seq<int>, key:int)
    requires intSeq == [1,3,5,7,9,11]
    ensures pre_binary(intSeq, key)
{}

lemma test_pre_binary_property(intSeq:seq<int>, key:int)
    requires forall i, j | 0 <= i < j < |intSeq| :: intSeq[i] < intSeq[j] 
    // note that this is a slightly stronger version than the precondition of binary search
    ensures pre_binary(intSeq, key);
{
}


/// non-realistic test ///
lemma test_pre_binary_non_realistic(intSeq:seq<int>, key:int)
    requires pre_binary(intSeq, key)
    ensures exists r :: post_binary(intSeq, key, r)
{
    if (forall i | 0 <= i < |intSeq| :: intSeq[i] != key) {
        assert post_binary(intSeq, key, -1);
    } else {
        var r :| 0 <= r < |intSeq| && intSeq[r] == key;
        assert post_binary(intSeq, key, r);
    }
}

/// provability tests - precondition ///
/*
1. 0 < i
2. true
*/
lemma test_pre_binary_provability_1(intSeq:seq<int>, key:int)
    requires intSeq == [2,1]
    ensures !pre_binary(intSeq, key)
{
    assert intSeq[0] > intSeq[1];
}

lemma test_pre_binary_provability_2(intSeq:seq<int>, key:int)
    requires intSeq == [5,4,3,2,1]
    ensures !pre_binary(intSeq, key)
{
    assert intSeq[0] > intSeq[1];
}

lemma test_pre_binary_provability_3(intSeq:seq<int>, key:int)
    requires intSeq == [5,4,4,2,1]
    ensures !pre_binary(intSeq, key)
{
    assert intSeq[0] > intSeq[1];
}

lemma test_pre_binary_provability_4(intSeq:seq<int>, key:int)
    requires intSeq == [5,1,2,3,4]
    ensures !pre_binary(intSeq, key)
{
    assert intSeq[0] > intSeq[1];
}

lemma test_pre_binary_provability_5(intSeq:seq<int>, key:int)
    requires intSeq == [1,2,3,4,1]
    ensures !pre_binary(intSeq, key)
{
    assert intSeq[3] > intSeq[4];
}

lemma test_pre_binary_provability_6(intSeq:seq<int>, key:int)
    requires intSeq == [3,2,1]
    ensures !pre_binary(intSeq, key)
{
    assert intSeq[0] > intSeq[1];
}

lemma test_pre_binary_provability_7(intSeq:seq<int>, key:int)
    requires intSeq == [1,3,2]
    ensures !pre_binary(intSeq, key)
{
    assert intSeq[1] > intSeq[2];
}
