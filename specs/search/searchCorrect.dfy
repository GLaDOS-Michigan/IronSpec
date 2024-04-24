
include "searchSpec.dfy"

module BinarySearch{
    import opened searchSpec

lemma BinarySearch(intSeq:seq<int>, key:int) returns (r:int)
    // original
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
    // ensures searchSpecCorrect(intSeq,key,r)
        ensures searchSpecIncorrectV2(intSeq,key,r)

{  
    // var lo:nat := 0;
    // var hi:nat := |intSeq|;
    // while lo < hi
    // invariant 0 <= lo <= hi <= |intSeq|
    // invariant forall i:nat | 0 <= i < lo :: intSeq[i] < key
    // invariant forall i:nat | hi <= i < |intSeq| :: intSeq[i] > key
    // {
    //     var mid := (lo + hi) / 2;
    //     if (intSeq[mid] < key) {
    //         lo := mid + 1;
    //     } else if (intSeq[mid] > key) {
    //         hi := mid;
    //     } else {
    //         return mid;
    //     }
    // }
    // return -1;
    var lo:nat := 0;
    var hi:nat := |intSeq|;
    while lo < hi
    invariant 0 <= lo <= hi <= |intSeq|
    invariant forall i:nat | 0 <= i < lo :: intSeq[i] < key
    invariant (forall i:nat | hi <= i < |intSeq| :: intSeq[i] > key)
        || (forall i:nat | hi <= i < |intSeq| :: intSeq[i] >= key && exists i:nat | lo <= i < hi :: intSeq[i] == key)
    {
        var mid := (lo + hi) / 2;
        if (intSeq[mid] < key) {
            lo := mid + 1;
        } else if (intSeq[mid] > key) {
            hi := mid;
        } else {
            assert intSeq[mid] == key;
            var inner_mid := (lo + mid) / 2;
            if (intSeq[inner_mid] < key) {
                lo := inner_mid + 1;
            } else if (hi != inner_mid + 1) {
                hi := inner_mid + 1;
            } else {
                if (intSeq[lo] == key) {
                    return lo;
                } else {
                    lo := lo + 1;
                }
            }
        }
    }
    return -1;
}

}