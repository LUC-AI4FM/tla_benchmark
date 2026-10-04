---------------------------- MODULE Quicksort ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS N

ASSUME NAssumption == N \in Nat \ {0}

VARIABLES arr, unsorted

vars == <<arr, unsorted>>

\* Helper: Check if seq2 is a permutation of seq1 over indices lo..hi
IsPermutationOver(seq1, seq2, lo, hi) ==
    /\ Len(seq1) = Len(seq2)
    /\ \A i \in 1..Len(seq1) : (i < lo \/ i > hi) => seq2[i] = seq1[i]
    /\ LET Bag1 == [v \in 1..N |-> Cardinality({i \in lo..hi : seq1[i] = v})]
           Bag2 == [v \in 1..N |-> Cardinality({i \in lo..hi : seq2[i] = v})]
       IN Bag1 = Bag2

\* Check if array is partitioned around pivot index p within interval lo..hi
IsPartitioned(seq, lo, hi, p) ==
    /\ lo <= p /\ p <= hi
    /\ \A i \in lo..(p-1) : seq[i] <= seq[p]
    /\ \A j \in (p+1)..hi : seq[p] <= seq[j]

\* All possible arrays that are valid partitions of arr around some pivot
ValidPartitions(seq, lo, hi, p) ==
    {newArr \in [1..N -> 1..N] : 
        /\ IsPermutationOver(seq, newArr, lo, hi)
        /\ IsPartitioned(newArr, lo, hi, p)}

\* Type invariant
TypeOK ==
    /\ arr \in [1..N -> 1..N]
    /\ unsorted \subseteq (1..N) \X (1..N)
    /\ \A interval \in unsorted : interval[1] <= interval[2]

\* Initial state: arbitrary array, entire range needs sorting
Init ==
    /\ arr \in [1..N -> 1..N]
    /\ unsorted = {<<1, N>>}

\* Partition step for interval with more than one element
Partition(lo, hi) ==
    /\ hi > lo
    /\ <<lo, hi>> \in unsorted
    /\ \E p \in lo..hi :
        \E newArr \in ValidPartitions(arr, lo, hi, p) :
            /\ arr' = newArr
            /\ unsorted' = (unsorted \ {<<lo, hi>>}) \cup
                           (IF p > lo THEN {<<lo, p-1>>} ELSE {}) \cup
                           (IF p < hi THEN {<<p+1, hi>>} ELSE {})

\* Remove trivial interval (length 0 or 1)
RemoveTrivial(lo, hi) ==
    /\ hi <= lo
    /\ <<lo, hi>> \in unsorted
    /\ unsorted' = unsorted \ {<<lo, hi>>}
    /\ arr' = arr

\* Next state relation
Next ==
    \E lo, hi \in 1..N :
        \/ Partition(lo, hi)
        \/ RemoveTrivial(lo, hi)

\* Fairness: weak fairness on all possible partition and remove actions
Fairness ==
    \A lo, hi \in 1..N :
        /\ WF_vars(Partition(lo, hi))
        /\ WF_vars(RemoveTrivial(lo, hi))

\* Specification
Spec == Init /\ [][Next]_vars /\ Fairness

\* Termination: eventually no unsorted intervals remain
Termination == <>(unsorted = {})

\* The array is sorted when algorithm terminates
IsSorted == \A i, j \in 1..N : i < j => arr[i] <= arr[j]

\* Safety: when unsorted is empty, array should be sorted
SortedWhenDone == (unsorted = {}) => IsSorted

\* The final array is a permutation of the initial array
\* (This is implicitly maintained by IsPermutationOver in each step)

==========================================================================