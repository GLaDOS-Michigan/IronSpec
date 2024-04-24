function method last(intSeq:array<int>):int
    reads intSeq
    requires intSeq.Length > 0
{
    intSeq[intSeq.Length - 1]
}

lemma multisetAdditivity(m1:multiset<int>, m2:multiset<int>, m3:multiset<int>, m4:multiset<int>)
    requires m1 == m2 + m3
    requires m1 == m2 + m4
    ensures m3 == m4
    {
        assert m3 == m1 - m2;
        assert m4 == m1 - m2;
    }
predicate post_multiset(m1:multiset<int>, m2:multiset<int>)
{
    m1 == m2
}

lemma test_multiset(m1:multiset<int>, m2:multiset<int>, m3:multiset<int>, m4:multiset<int>)
    requires |m3| != |m4|
    ensures !post_multiset(m3, m4)
{}

lemma multisetMinus(intSeq1:seq<int>, intSeq2:seq<int>, start:nat, end:nat)
    requires multiset(intSeq1) == multiset(intSeq2)
    requires |intSeq1| == |intSeq2|
    requires 0 <= start <= end <= |intSeq1|
    requires forall i:nat | i < start || end <= i < |intSeq1| ::intSeq1[i] == intSeq2[i]
    ensures multiset(intSeq1[start..end]) == multiset(intSeq2[start..end])
    {
        assert intSeq1[0..start] == intSeq2[0..start];
        assert multiset(intSeq1[0..start]) == multiset(intSeq2[0..start]);
        assert intSeq1[end..|intSeq1|] == intSeq2[end..|intSeq1|];
        assert multiset(intSeq1[end..|intSeq1|]) == multiset(intSeq2[end..|intSeq1|]);
        assert intSeq1 == intSeq1[0..start] + intSeq1[start..end] + intSeq1[end..|intSeq1|];
        assert multiset(intSeq1) == multiset(intSeq1[0..start]) + multiset(intSeq1[start..end]) + multiset(intSeq1[end..|intSeq1|]);
        assert intSeq2 == intSeq2[0..start] + intSeq2[start..end] + intSeq2[end..|intSeq1|];
        assert multiset(intSeq2) == multiset(intSeq2[0..start]) + multiset(intSeq2[start..end]) + multiset(intSeq2[end..|intSeq1|]);
        multisetAdditivity(multiset(intSeq1), multiset(intSeq1[0..start]) + multiset(intSeq1[end..|intSeq1|]), multiset(intSeq1[start..end]), multiset(intSeq2[start..end]));

    }
    
method quickSort(intSeq:array<int>)
    modifies intSeq
    ensures forall i:nat, j:nat | 0 <= i <= j < intSeq.Length :: intSeq[i] <= intSeq[j]
    ensures multiset(intSeq[..]) == multiset(old(intSeq[..]))
    {
        quickSortRec(intSeq, 0, intSeq.Length);
    }



method quickSortRec(intSeq:array<int>, start:nat, end:nat)
    requires 0 <= start <= end <= intSeq.Length
    decreases end - start
    modifies intSeq
    ensures forall i:nat | i < start || end <= i < intSeq.Length :: intSeq[i] == old(intSeq[i])
    ensures forall i:nat, j:nat | start <= i <= j < end :: intSeq[i] <= intSeq[j]
    ensures multiset(intSeq[..]) == multiset(old(intSeq[..]))
{
    if (end - start <= 1) {
        return;
    } else {
        var pivot := intSeq[end - 1];
        var largePartStart := start;
        var idx := start;
        while idx < end - 1
            modifies intSeq
            invariant start <= largePartStart <= idx <= end - 1
            invariant forall i:nat | start <= i < largePartStart :: intSeq[i] <= pivot
            invariant forall i:nat | largePartStart <= i < idx :: intSeq[i] > pivot
            invariant pivot == intSeq[end - 1]
            invariant multiset(intSeq[..]) == multiset(old(intSeq[..]))
            invariant forall i:nat | i < start || end <= i < intSeq.Length :: intSeq[i] == old(intSeq[i])

        {
            if (intSeq[idx] <= pivot) {
                intSeq[largePartStart], intSeq[idx] := intSeq[idx], intSeq[largePartStart];
                largePartStart := largePartStart + 1;
            }
            idx := idx + 1;
        }
        assert forall i:nat | start <= i < largePartStart :: intSeq[i] <= pivot;
        assert forall i:nat | largePartStart <= i < end - 1 :: intSeq[i] > pivot;

        ghost var temp := intSeq[largePartStart];
        assert temp >= pivot by {
            if (largePartStart < end - 1) {
                assert temp > pivot;
            } else {
                assert largePartStart == end - 1;
                assert pivot == temp;
            }
        }
        assert end - 1 >= largePartStart;
        intSeq[end - 1] := intSeq[largePartStart];
        assert intSeq[end - 1] >= pivot;
        intSeq[largePartStart] := pivot;
        assert intSeq[largePartStart] == pivot;

        var copy1 := intSeq[..];
        quickSortRec(intSeq, start, largePartStart);
        var copy2 := intSeq[..];
        quickSortRec(intSeq, largePartStart + 1, end);

        forall i:nat | start <= i < largePartStart
            ensures intSeq[i] <= pivot {
                assert intSeq[i] in copy2[start..largePartStart];
                assert multiset(copy1) == multiset(copy2);
                multisetMinus(copy2, copy1, start, largePartStart);
                assert multiset(copy1[start..largePartStart]) == multiset(copy2[start..largePartStart]);
                assert intSeq[i] in multiset(copy2[start..largePartStart]);
                assert intSeq[i] in copy1[start..largePartStart];
            }
        assert intSeq[largePartStart] == pivot;
        forall i:nat | largePartStart < i < end 
            ensures intSeq[i] >= pivot {
                multisetMinus(intSeq[..], copy2, largePartStart + 1, end);
                assert intSeq[i] in multiset(intSeq[..]);
                assert intSeq[i] in multiset(copy2[largePartStart + 1..end]);
                assert intSeq[i] in copy2[largePartStart + 1..end];
            }

    }
}

