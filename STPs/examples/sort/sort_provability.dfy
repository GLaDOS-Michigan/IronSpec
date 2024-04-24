include "sort.dfy"

/*
1. <= -> <

*/

// to check it is implementable
lemma test_post_sort_realistic_point_1(prevSeq:seq<int>, curSeq:seq<int>)
    requires prevSeq == []
    requires curSeq == []
    ensures post_sort(prevSeq, curSeq)
{
}

lemma test_post_sort_realistic_point_2(prevSeq:seq<int>, curSeq:seq<int>)
    requires |prevSeq| == 1
    requires curSeq == prevSeq
    ensures post_sort(prevSeq, curSeq)
{
}

lemma test_post_sort_realistic_point_3(prevSeq:seq<int>, curSeq:seq<int>)
    requires prevSeq == [1,1,2,2,4]
    requires curSeq == prevSeq
    ensures post_sort(prevSeq, curSeq)
{
}

lemma test_post_sort_realistic_point_4(prevSeq:seq<int>, curSeq:seq<int>)
    requires prevSeq == [1,3,2,4]
    requires curSeq == [1,2,3,4]
    ensures post_sort(prevSeq, curSeq)
{
}

lemma test_post_sort_realistic_point_5(prevSeq:seq<int>, curSeq:seq<int>)
    requires prevSeq == [4,3,2,1]
    requires curSeq == [1,2,3,4]
    ensures post_sort(prevSeq, curSeq)
{
}

lemma test_post_sort_realistic_point_6(prevSeq:seq<int>, curSeq:seq<int>)
    requires prevSeq == [2,2]
    requires curSeq == [2,2]
    ensures post_sort(prevSeq, curSeq)
{
}

lemma test_post_sort_realistic_point_7(prevSeq:seq<int>, curSeq:seq<int>)
    requires prevSeq == [1,2,3,4]
    requires curSeq == [1,2,3,4]
    ensures post_sort(prevSeq, curSeq)
{
}

lemma test_post_sort_realistic_point_8(prevSeq:seq<int>, curSeq:seq<int>)
    requires prevSeq == [1,3,5,7,9,11]
    requires curSeq == [1,3,5,7,9,11]
    ensures post_sort(prevSeq, curSeq)
{
}

lemma test_post_sort_provability(prevSeq:seq<int>, curSeq:seq<int>)
    requires forall i, j | 0 <= i <= j < |prevSeq| :: prevSeq[i] <= prevSeq[j] // input is sorted
    requires curSeq == prevSeq
    ensures post_sort(prevSeq, curSeq)
{}
