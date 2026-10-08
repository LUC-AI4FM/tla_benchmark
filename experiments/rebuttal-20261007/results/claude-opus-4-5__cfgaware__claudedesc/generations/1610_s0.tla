---------------------------- MODULE quicksort ----------------------------

EXTENDS Naturals, Sequences, FiniteSets

CONSTANT N

VARIABLES Ainit, A, S, pivot, pc

vars == <<Ainit, A, S, pivot, pc>>

Perms(arr, lo, hi) ==
    { B \in [1..N -> 1..N] :
        /\ \A i \in 1..N : (i < lo \/ i > hi) => B[i] = arr[i]
        /\ \E perm \in [lo..hi -> lo..hi] :
            /\ \A i \in lo..hi : \E j \in lo..hi : perm[j] = i
            /\ \A i \in lo..hi : B[i] = arr[perm[i]] }

Partitioned(arr, lo, p, hi) ==
    /\ \A i \in lo..(p-1) : \A j \in p..hi : arr[i] <= arr[j]

Init ==
    /\ Ainit \in [1..N -> 1..N]
    /\ A = Ainit
    /\ S = {<<1, N>>}
    /\ pivot = 1
    /\ pc = "qs1"

qs1 ==
    /\ pc = "qs1"
    /\ S /= {}
    /\ \E I \in S :
        IF I[1] < I[2]
        THEN \E piv \in I[1]..I[2] :
             \E B \in Perms(A, I[1], I[2]) :
                /\ Partitioned(B, I[1], piv, I[2])
                /\ A' = B
                /\ pivot' = piv
                /\ S' = (S \ {I}) \cup 
                        (IF piv > I[1] THEN {<<I[1], piv - 1>>} ELSE {}) \cup
                        (IF piv < I[2] THEN {<<piv + 1, I[2]>>} ELSE {})
                /\ Ainit' = Ainit
                /\ pc' = "qs1"
        ELSE
            /\ S' = S \ {I}
            /\ A' = A
            /\ pivot' = pivot
            /\ Ainit' = Ainit
            /\ pc' = "qs1"

Done ==
    /\ pc = "qs1"
    /\ S = {}
    /\ pc' = "Done"
    /\ UNCHANGED <<Ainit, A, S, pivot>>

Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == qs1 \/ Done \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

==========================================================================