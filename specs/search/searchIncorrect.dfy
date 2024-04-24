
include "searchSpec.dfy"

module BinarySearch{
    import opened searchSpec

// lemma BinarySearch(intSeq:seq<int>, key:int) returns (r:int)
//     // original
//     requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
//     ensures searchSpecIncorrect(intSeq,key,r)
// {  
//     var lo:nat := 0;
//     var hi:nat := |intSeq|;
//     while lo < hi
//     invariant 0 <= lo <= hi <= |intSeq|
//     invariant forall i:nat | 0 <= i < lo :: intSeq[i] < key
//     invariant forall i:nat | hi <= i < |intSeq| :: intSeq[i] > key
//     {
//         var mid := (lo + hi) / 2;
//         if (intSeq[mid] < key) {
//             lo := mid + 1;
//         } else if (intSeq[mid] > key) {
//             hi := mid;
//         } else {
//             return mid;
//         }
//     }
//     return -1;
// }


lemma BinarySearchIncorrect(intSeq:seq<int>, key:int) returns (r:int)
    // original
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
    ensures searchSpecIncorrectV2(intSeq,key,r)
{  
    // return 0;
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
            return 0;
        }
    }
    return -1;
}

}