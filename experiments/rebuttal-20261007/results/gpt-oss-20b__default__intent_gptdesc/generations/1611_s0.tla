MODULE MergeSort
EXTENDS Naturals, Sequences

CONSTANTS N, initArr

VARIABLE arr, unsorted, sorted

(* Helper functions *)
LenI(I) == I.hi - I.lo + 1
Mid(I) == (I.lo + I.hi) \div 2
Left(I) == [lo |-> I.lo, hi |-> Mid(I)]
Right(I) == [lo |-> Mid(I)+1, hi |-> I.hi]
WholeInterval == [lo |-> 1, hi |-> N]

SortedSubarray(a, I) ==
  \A i,j \in 1..Len(a) :
    (I.lo <= i /\ i < j /\ j <= I.hi) => a[i] <= a[j]

Count(v, seq) == Len({ i \in 1..Len(seq) : seq[i] = v })
CountInSubarray(v, seq, lo, hi) ==
  Len({ i \in lo..hi : seq[i] = v })

SetInSubseq(seq, lo, hi) == \{ e \in seq[lo..hi] : TRUE \}

MERGE_OK(a, a', I) ==
  /\ \A k \in 1..Len(a) :
       (k < I.lo \/ k > I.hi) => a'[k] = a[k]
  /\ SortedSubarray(a', I)
  /\ \A v \in SetInSubseq(a, I.lo, I.hi) :
        CountInSubarray(v, a', I.lo, I.hi) =
        CountInSubarray(v, a, I.lo, I.hi)

PermutationInvariant ==
  \A v \in \{ e \in initArr : TRUE \} :
    Count(v, arr) = Count(v, initArr)

Terminated == unsorted = {} /\ sorted = {WholeInterval}

SortednessAfterTermination ==
  Terminated => SortedSubarray(arr, WholeInterval)

BaseCase ==
  \E I \in unsorted :
    LenI(I) = 1 /\
    arr' = arr /\
    unsorted' = unsorted \ {I} /\
    sorted' = sorted ∪ {I}

SplitAction ==
  \E I \in unsorted :
    LenI(I) > 1 /\ 
    arr' = arr /\
    unsorted' = (unsorted \ {I}) ∪ {Left(I), Right(I)} /\
    sorted' = sorted

MergeAction ==
  \E I \in unsorted :
    LenI(I) > 1 /\ 
    Left(I) \in sorted /\ Right(I) \in sorted /\
    MERGE_OK(arr, arr', I) /\
    unsorted' = unsorted \ {I} /\
    sorted' = (sorted \ {Left(I), Right(I)}) ∪ {I}

Next == BaseCase \/ SplitAction \/ MergeAction

Init ==
  /\ Len(initArr) = N
  /\ arr = initArr
  /\ unsorted = {WholeInterval}
  /\ sorted = {}

Spec == Init /\ [][Next]_vars /\ <> Terminated /\ []PermutationInvariant /\ []SortednessAfterTermination

END MODULE