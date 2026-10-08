---------------------------- MODULE Quicksort ----------------------------

EXTENDS Integers, Sequences, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N > 0

VARIABLES arr, intervals

vars == <<arr, intervals>>

\* Helper: Check if seq2 is a permutation of seq1 over indices lo..hi
IsPermutationOver(seq1, seq2, lo, hi) ==
    /\ \A i \in lo..hi : seq2[i] \in {seq1[j] : j \in lo..hi}
    /\ \A v \in {seq1[j] : j \in lo..hi} :
        Cardinality({i \in lo..hi : seq2[i] = v}) = Cardinality({i \in lo..hi : seq1[i] = v})

\* Helper: Check if arrangement is valid after partitioning around pivot index p
IsValidPartition(oldArr, newArr, lo, hi, p) ==
    /\ IsPermutationOver(oldArr, newArr, lo, hi)
    /\ \A i \in lo..(p-1) : \A j \in (p+1)..hi : newArr[i] <= newArr[j]
    /\ \A i \in lo..(p-1) : newArr[i] <= newArr[p]
    /\ \A j \in (p+1)..hi : newArr[p] <= newArr[j]
    /\ \A i \in 1..N : (i < lo \/ i > hi) => newArr[i] = oldArr[i]

\* Initial state: array is some permutation of 1..N, intervals contains the full range
Init ==
    /\ arr \in [1..N -> 1..N]
    /\ \A v \in 1..N : Cardinality({i \in 1..N : arr[i] = v}) = 1
    /\ intervals = {<<1, N>>}

\* Partition step: choose an interval, partition it
Partition ==
    /\ intervals /= {}
    /\ \E interval \in intervals :
        LET lo == interval[1]
            hi == interval[2]
        IN
        IF hi - lo < 1
        THEN \* Interval of size 0 or 1, just remove it
            /\ intervals' = intervals \ {interval}
            /\ arr' = arr
        ELSE \* Partition the interval
            /\ \E p \in lo..hi :  \* Choose pivot position nondeterministically
                /\ \E newArr \in [1..N -> 1..N] :
                    /\ IsValidPartition(arr, newArr, lo, hi, p)
                    /\ arr' = newArr
                    /\ intervals' = (intervals \ {interval}) \cup 
                        (IF p > lo THEN {<<lo, p-1>>} ELSE {}) \cup
                        (IF p < hi THEN {<<p+1, hi>>} ELSE {})

\* Termination: do nothing when done
Done ==
    /\ intervals = {}
    /\ UNCHANGED vars

Next == Partition \/ Done

\* Fairness: weak fairness on the next step to ensure progress
Fairness == WF_vars(Partition)

Spec == Init /\ [][Next]_vars /\ Fairness

\* Termination property: eventually no intervals remain
Termination == <>(intervals = {})

==========================================================================