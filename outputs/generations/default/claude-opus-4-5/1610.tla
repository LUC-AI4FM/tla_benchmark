------------------------------ MODULE Quicksort ------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS N

ASSUME NAssumption == N \in Nat /\ N >= 1

VARIABLES arr, S, pc

vars == <<arr, S, pc>>

\* Helper: Set of all permutations of a sequence
PermutationsOf(seq) ==
    LET Domain == 1..Len(seq)
        Range == {seq[i] : i \in Domain}
    IN {perm \in [Domain -> Range] : 
        /\ \A i, j \in Domain : i /= j => perm[i] /= perm[j]
        /\ {perm[i] : i \in Domain} = Range}

\* Check if arr restricted to lo..hi is a permutation of original restricted to lo..hi
IsPermutationOnRange(newArr, oldArr, lo, hi) ==
    LET indices == lo..hi
        oldValues == [i \in indices |-> oldArr[i]]
        newValues == [i \in indices |-> newArr[i]]
    IN /\ {newValues[i] : i \in indices} = {oldValues[i] : i \in indices}
       /\ Cardinality({<<i, newValues[i]>> : i \in indices}) = hi - lo + 1

\* Check partition property: elements before pivot <= pivot value, elements after >= pivot value
SatisfiesPartition(newArr, lo, hi, pivotPos) ==
    /\ \A i \in lo..(pivotPos-1) : newArr[i] <= newArr[pivotPos]
    /\ \A i \in (pivotPos+1)..hi : newArr[i] >= newArr[pivotPos]

\* All arrays of length N with values in 1..N
Arrays == [1..N -> 1..N]

\* Type invariant
TypeOK ==
    /\ arr \in Arrays
    /\ S \subseteq (1..N) \X (1..N)
    /\ pc \in {"qs1", "Done"}

Init ==
    /\ arr \in Arrays
    /\ S = {<<1, N>>}
    /\ pc = "qs1"

\* Main quicksort step: process one interval from S
qs1 ==
    /\ pc = "qs1"
    /\ IF S = {}
       THEN /\ pc' = "Done"
            /\ arr' = arr
            /\ S' = S
       ELSE \E interval \in S :
            LET lo == interval[1]
                hi == interval[2]
            IN IF lo >= hi
               THEN \* Interval has 0 or 1 elements, just remove it
                    /\ S' = S \ {interval}
                    /\ arr' = arr
                    /\ pc' = "qs1"
               ELSE \* Partition the interval
                    \E pivotPos \in lo..hi :
                    \E newArr \in Arrays :
                        /\ \A i \in 1..N : (i < lo \/ i > hi) => newArr[i] = arr[i]
                        /\ IsPermutationOnRange(newArr, arr, lo, hi)
                        /\ SatisfiesPartition(newArr, lo, hi, pivotPos)
                        /\ arr' = newArr
                        /\ S' = (S \ {interval}) \cup 
                                (IF pivotPos > lo THEN {<<lo, pivotPos - 1>>} ELSE {}) \cup
                                (IF pivotPos < hi THEN {<<pivotPos + 1, hi>>} ELSE {})
                        /\ pc' = "qs1"

Next == qs1

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Termination property
Termination == <>(pc = "Done")

=============================================================================