
module searchSpec
{
    predicate searchSpecCorrect(intSeq:seq<int>, key:int, r:int)
        requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]

    {
         && (r >= 0 ==> r < |intSeq| && intSeq[r] == key)
         && (r < 0 ==> forall i:nat | i < |intSeq| :: intSeq[i] != key)
         && (r < 0 ==> r == -1) // return -1 if not found
         && (r >= 0 ==> forall i:nat | i < r :: intSeq[i] < key)
    }

    predicate searchSpecIncorrect(intSeq:seq<int>, key:int, r:int)
        requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]

    {
     && (r >= 0 ==> r < |intSeq| && intSeq[r] == key)
     && (r < 0 ==> forall i:nat | 0 < i && i < |intSeq| :: intSeq[i] != key) // i >= 0

    }

    predicate searchSpecIncorrectV2(intSeq:seq<int>, key:int, r:int)
        requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]

    {
         && (r > 0 ==> r < |intSeq| && intSeq[r] == key)
         && (r < 0 ==> forall i:nat | i < |intSeq| :: intSeq[i] != key)
         && (r < 0 ==> r == -1) // return -1 if not found
         && (r >= 0 ==> forall i:nat | i < r :: intSeq[i] < key)

    }
}



