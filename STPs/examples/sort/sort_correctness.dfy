include "sort.dfy"

/*
1. no multiset line
2. 0<
3. multiset <=
4. multiset >=
*/

// to check it is functioning
// postcondition
// iterate cases from the point of view of inputs' variation
lemma test_post_sort_point_1(prevSeq:seq<int>, curSeq:seq<int>)
    requires |curSeq| != |prevSeq|
    ensures !post_sort(prevSeq, curSeq)
{
    assert |multiset(curSeq)| != |multiset(prevSeq)|;
}

// lemma test_post_sort_point_1'(prevSeq:seq<int>, curSeq:seq<int>)
//     requires prevSeq == [3,2,1]
//     requires |curSeq| != |prevSeq|
//     ensures !post_sort(prevSeq, curSeq)
// {}

lemma test_post_sort_point_2(prevSeq:seq<int>, curSeq:seq<int>)
    requires prevSeq == [3,2,1]
    requires post_sort(prevSeq, curSeq)
    ensures curSeq == [1,2,3]
{}

lemma test_post_sort_point_3(prevSeq:seq<int>, curSeq:seq<int>)
    requires |prevSeq| == 1
    requires curSeq != prevSeq
    ensures !post_sort(prevSeq, curSeq)
{
    assert post_sort(prevSeq, [prevSeq[0]]);
}

// // sometimes a specific case is easier to prove
// lemma test_post_sort_point_3'(prevSeq:seq<int>, curSeq:seq<int>)
//     requires prevSeq == [0]
//     requires curSeq != prevSeq
//     ensures !post_sort(prevSeq, curSeq)
// {}
lemma test_post_sort_point_4(prevSeq:seq<int>, curSeq:seq<int>)
    requires prevSeq == [2,2]
    requires curSeq != prevSeq
    ensures !post_sort(prevSeq, curSeq)
{
    if (|curSeq| == 2)
    {
        assert || curSeq[0] !=2
            || curSeq[1] != 2;
        assert curSeq[0] in multiset(curSeq);
        assert curSeq[1] in multiset(curSeq);
        assert multiset(curSeq) != multiset{2,2};
    }
}

lemma test_post_sort_point_5(prevSeq:seq<int>, curSeq:seq<int>)
    requires prevSeq == [1,2,2,4]
    requires curSeq == [1,2,3,4]
    ensures !post_sort(prevSeq, curSeq)
{
}

lemma test_post_sort_point_5'(prevSeq:seq<int>, curSeq:seq<int>)
    requires prevSeq == [1,2,2,4]
    requires curSeq == [1,2,4,2]
    ensures !post_sort(prevSeq, curSeq)
{
    assert curSeq[2] > curSeq[3];
}

lemma test_post_sort_point_5''(prevSeq:seq<int>, curSeq:seq<int>)
    requires prevSeq == [1,2,2,4]
    requires curSeq == [1,1,2,4]
    ensures !post_sort(prevSeq, curSeq)
{
}

lemma test_post_sort_point_6(prevSeq:seq<int>, curSeq:seq<int>)
    requires prevSeq == [1,2,3,4]
    requires curSeq != prevSeq
    ensures !post_sort(prevSeq, curSeq)
{}

lemma test_post_sort_point_7(prevSeq:seq<int>, curSeq:seq<int>)
    requires prevSeq == [1,3,5,7,9,11]
    requires curSeq != prevSeq
    ensures !post_sort(prevSeq, curSeq)
{}

lemma test_post_sort_point_8(prevSeq:seq<int>, curSeq:seq<int>)
    requires prevSeq == [1,3,2,4]
    requires curSeq != [1,2,3,4]
    ensures !post_sort(prevSeq, curSeq)
{}

lemma test_post_sort_point_9(prevSeq:seq<int>, curSeq:seq<int>)
    requires prevSeq == [4,3,2,1]
    requires curSeq != [1,2,3,4]
    ensures !post_sort(prevSeq, curSeq)
{}

lemma test_post_sort_vertical_1(prevSeq:seq<int>, curSeq:seq<int>)
    requires post_sort(prevSeq, curSeq)
    ensures |prevSeq| > 0 ==> |curSeq| > 0
    ensures |prevSeq| > 0 ==> curSeq[0] in prevSeq
{
    if (|prevSeq| > 0) {
        assert |multiset(prevSeq)| == |multiset(curSeq)|;
        assert curSeq[0] in multiset(prevSeq);
    }
}

// lemma test_post_sort_vertical_1'(prevSeq:seq<int>, curSeq:seq<int>)
//     requires |prevSeq| > 0
//     requires |curSeq| > 0
//     requires curSeq[0] !in prevSeq
//     ensures  !post_sort(prevSeq, curSeq)
// {
//     assert curSeq[0] !in multiset(prevSeq);
// }