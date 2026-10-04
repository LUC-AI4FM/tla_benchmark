---------------------------- MODULE QuickSort ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS N

ASSUME N \in Nat /\ N >= 1

VARIABLES arr, S, pc

vars == <<arr, S, pc>>

\* A permutation of a sequence is another sequence with the same elements
IsPermutation(s1, s2) ==
    /\ Len(s1) = Len(s2)
    /\ \A i \in 1..Len(s1) : 
        Cardinality({j \in 1..Len(s1) : s1[j] = i}) = 
        Cardinality({j \in 1..Len(s2) : s2[j] = i})

\* Check if array segment [lo..hi] satisfies partition property around pivot position p
\* All elements in [lo..p-1] <= arr[p] and all elements in [p+1..hi] >= arr[p]
SatisfiesPartition(a, lo, hi, p) ==
    /\ \A i \in lo..(p-1) : a[i] <= a[p]
    /\ \A i \in (p+1)..hi : a[i] >= a[p]

\* Check if new array is a valid partitioned permutation of segment [lo..hi]
\* The segment [lo..hi] in the new array is a permutation of the same segment in the old array
\* and satisfies the partition property
ValidPartitionedArray(oldArr, newArr, lo, hi, p) ==
    /\ \A i \in 1..N : (i < lo \/ i > hi) => newArr[i] = oldArr[i]
    /\ [i \in 1..(hi-lo+1) |-> newArr[lo+i-1]] \in 
       {s \in [1..(hi-lo+1) -> 1..N] : 
        \A v \in 1..N : Cardinality({j \in 1..(hi-lo+1) : s[j] = v}) = 
                        Cardinality({j \in lo..hi : oldArr[j] = v})}
    /\ SatisfiesPartition(newArr, lo, hi, p)

\* All possible arrays of length N with values in 1..N
Arrays == [1..N -> 1..N]

\* Initial state
Init ==
    /\ arr \in Arrays
    /\ S = {<<1, N>>}
    /\ pc = "qs1"

\* Main quicksort step: pick an interval, choose pivot, partition
qs1 ==
    /\ pc = "qs1"
    /\ IF S = {}
       THEN /\ pc' = "Done"
            /\ arr' = arr
            /\ S' = S
       ELSE \E interval \in S :
            LET lo == interval[1]
                hi == interval[2]
            IN
            IF lo >= hi
            THEN /\ S' = S \ {interval}
                 /\ arr' = arr
                 /\ pc' = "qs1"
            ELSE \E p \in lo..hi :  \* Nondeterministically choose pivot position
                 \E newArr \in Arrays :  \* Nondeterministically choose new array
                    /\ ValidPartitionedArray(arr, newArr, lo, hi, p)
                    /\ arr' = newArr
                    /\ S' = (S \ {interval}) \cup 
                            (IF p > lo THEN {<<lo, p-1>>} ELSE {}) \cup
                            (IF p < hi THEN {<<p+1, hi>>} ELSE {})
                    /\ pc' = "qs1"

\* Termination state
Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

\* Next-state relation
Next == qs1 \/ Terminating

\* Specification with weak fairness
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Type invariant
TypeOK ==
    /\ arr \in Arrays
    /\ S \subseteq {<<i, j>> : i \in 1..N, j \in 1..N}
    /\ pc \in {"qs1", "Done"}

\* Safety: intervals in S are valid (lo <= hi when present, and within bounds)
SafeIntervals ==
    \A interval \in S : 
        /\ interval[1] \in 1..N
        /\ interval[2] \in 1..N

\* Liveness: eventual termination
Termination == <>(pc = "Done")

==========================================================================