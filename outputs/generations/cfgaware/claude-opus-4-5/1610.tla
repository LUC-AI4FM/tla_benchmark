-------------------------- MODULE quicksort --------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT N

VARIABLES A, S, pc

vars == <<A, S, pc>>

Perms(arr, lo, hi) ==
    {arr2 \in [1..N -> 1..N] : 
        /\ \A i \in 1..N : (i < lo \/ i > hi) => arr2[i] = arr[i]
        /\ \A v \in 1..N : 
            Cardinality({i \in lo..hi : arr2[i] = v}) = 
            Cardinality({i \in lo..hi : arr[i] = v})}

Partitioned(arr, lo, hi, p) ==
    /\ \A i \in lo..(p-1) : arr[i] <= arr[p]
    /\ \A i \in (p+1)..hi : arr[i] >= arr[p]

Init ==
    /\ A \in [1..N -> 1..N]
    /\ S = {<<1, N>>}
    /\ pc = "qs1"

qs1 ==
    /\ pc = "qs1"
    /\ IF S # {}
       THEN \E interval \in S :
                LET lo == interval[1]
                    hi == interval[2]
                IN
                /\ IF lo < hi
                   THEN \E p \in lo..hi :
                        \E A2 \in Perms(A, lo, hi) :
                            /\ Partitioned(A2, lo, hi, p)
                            /\ A' = A2
                            /\ S' = (S \ {interval}) \cup 
                                    (IF lo < p-1 THEN {<<lo, p-1>>} ELSE {}) \cup
                                    (IF p+1 < hi THEN {<<p+1, hi>>} ELSE {})
                   ELSE /\ A' = A
                        /\ S' = S \ {interval}
                /\ pc' = "qs1"
       ELSE /\ pc' = "Done"
            /\ A' = A
            /\ S' = S

Next ==
    \/ qs1
    \/ (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

=============================================================================