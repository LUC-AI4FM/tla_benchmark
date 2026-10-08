-------------------------------- MODULE QuickSort --------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT N

ASSUME N \in Nat /\ N >= 0

VARIABLES arr, pending, init_arr

vars == <<arr, pending, init_arr>>

\* Domain of values - we use 1..N for simplicity but could be any totally ordered set
Values == 1..N

\* Helper: Check if seq1 is a permutation of seq2 (multiset equality)
IsPermutation(seq1, seq2) ==
    /\ Len(seq1) = Len(seq2)
    /\ \A v \in Values : 
        Cardinality({i \in 1..Len(seq1) : seq1[i] = v}) = 
        Cardinality({i \in 1..Len(seq2) : seq2[i] = v})

\* Helper: Check if a sequence is sorted in nondecreasing order
IsSorted(seq) ==
    \A i, j \in 1..Len(seq) : i < j => seq[i] <= seq[j]

\* Helper: Extract subsequence from lo to hi
SubSeq(seq, lo, hi) ==
    IF lo > hi THEN <<>>
    ELSE [i \in 1..(hi - lo + 1) |-> seq[lo + i - 1]]

\* Helper: Check if all elements in range [lo1, hi1] are <= all elements in [lo2, hi2]
AllLessOrEqual(seq, lo1, hi1, lo2, hi2) ==
    \A i \in lo1..hi1, j \in lo2..hi2 : seq[i] <= seq[j]

\* Helper: Check if two sequences have same elements outside interval [lo, hi]
PreservesOutside(seq1, seq2, lo, hi) ==
    \A i \in 1..Len(seq1) : (i < lo \/ i > hi) => seq1[i] = seq2[i]

\* Helper: Check if seq2 is a rearrangement of seq1 within [lo, hi]
IsRearrangementWithin(seq1, seq2, lo, hi) ==
    /\ Len(seq1) = Len(seq2)
    /\ PreservesOutside(seq1, seq2, lo, hi)
    /\ \A v \in Values :
        Cardinality({i \in lo..hi : seq1[i] = v}) =
        Cardinality({i \in lo..hi : seq2[i] = v})

\* Initial state: array is any sequence of N values, pending contains the full interval
Init ==
    /\ arr \in [1..N -> Values]
    /\ pending = IF N > 0 THEN {<<1, N>>} ELSE {}
    /\ init_arr = arr

\* Type invariant
TypeOK ==
    /\ arr \in [1..N -> Values]
    /\ pending \subseteq {<<lo, hi>> : lo, hi \in 1..N}
    /\ init_arr \in [1..N -> Values]

\* Partition action: pick interval, choose pivot, rearrange array
Partition(lo, hi) ==
    /\ <<lo, hi>> \in pending
    /\ lo < hi
    /\ \E p \in lo..(hi-1) :
        \E newArr \in [1..N -> Values] :
            /\ IsRearrangementWithin(arr, newArr, lo, hi)
            /\ AllLessOrEqual(newArr, lo, p, p+1, hi)
            /\ arr' = newArr
            /\ pending' = (pending \ {<<lo, hi>>}) \union {<<lo, p>>, <<p+1, hi>>}
            /\ init_arr' = init_arr

\* Remove trivial interval (lo >= hi means 0 or 1 element, already sorted)
RemoveTrivial(lo, hi) ==
    /\ <<lo, hi>> \in pending
    /\ lo >= hi
    /\ pending' = pending \ {<<lo, hi>>}
    /\ arr' = arr
    /\ init_arr' = init_arr

\* Next state relation
Next ==
    \E lo, hi \in 1..N :
        \/ Partition(lo, hi)
        \/ RemoveTrivial(lo, hi)

\* Fairness: weak fairness on all enabled partition/remove actions
Fairness ==
    \A lo, hi \in 1..N :
        /\ WF_vars(Partition(lo, hi))
        /\ WF_vars(RemoveTrivial(lo, hi))

\* Complete specification with fairness
Spec == Init /\ [][Next]_vars /\ Fairness

\* ====================