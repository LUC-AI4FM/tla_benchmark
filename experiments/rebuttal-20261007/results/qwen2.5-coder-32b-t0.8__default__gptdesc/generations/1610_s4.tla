------------------------------- MODULE Quicksort -------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS N
ASSUME N > 0

VARIABLES arr, pc, S

Init == /\ arr \in [1..N -> 1..N]
        /\ pc = "qs1"
        /\ S = {[1, N]}

PivotSelect(subarr) == CHOOSE p \in subarr : TRUE

Partition(arr, pivot, lo, hi) ==
    LET less = {i \in lo..hi: arr[i] < pivot}
        greater = {i \in lo..hi: arr[i] > pivot}
        equal = {i \in lo..hi: arr[i] = pivot}
        newarr == [arr EXCEPT ![lo + Cardinality(less) + 1..lo + Cardinality(less) + Cardinality(equal)] <- (equal -> pivot)]
    IN CHOOSE perm \in Permutations(greater): 
            /\ (newarr' == [newarr EXCEPT ![lo..lo + Cardinality(less) - 1] <- perm[Take(lo, less)],
                                    ![lo + Cardinality(less) + Cardinality(equal) + 1..hi] <- perm[Drop(lo, greater)]])
            /\ \A i \in lo..lo + Cardinality(less) - 1 : newarr'[i] < pivot
            /\ \A i \in lo + Cardinality(less) + Cardinality(equal) + 1..hi : newarr'[i] > pivot

Next ==
    CASE pc = "qs1" ->
        \/ S = {}
           /\ pc' = "Done"
        \/ CHOOSE subarr \in S:
            LET pivot == PivotSelect(subarr)
                lo == Fst(subarr)
                hi ==_snd(subarr)
                newS == (IF lo < hi THEN
                            S \ {subarr} \cup {[lo, lo + Cardinality({i \in lo..hi: arr[i] < pivot}) - 1],
                                               [lo + Cardinality({i \in lo..hi: arr[i] <= pivot}) + 1, hi]}
                         ELSE
                            S \ {subarr})
            IN /\ Partition(arr, pivot, lo, hi) -> arr'
               /\ S' = newS

Spec ==
    /\ Init
    /\ [][Next]_<<pc>>
    /\ WF_next(<<pc>>)

=============================================================================