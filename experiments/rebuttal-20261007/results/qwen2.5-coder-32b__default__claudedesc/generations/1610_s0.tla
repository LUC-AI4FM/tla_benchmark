------------------------------- MODULE QuickSort -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N

VARIABLES Ainit, A, S, pivot, pc

Init == /\ Ainit \in [1..N -> 1..N]
        /\ A = Ainit
        /\ S = {<<1, N>>}
        /\ pc = "Start"

Next ==
    \/ /\ pc = "Start"
       /\ S /= {}
       /\ <<i, j>> \in S
       /\ i < j
       /\ pivot \in i..j
       /\ A' = [k \in 1..N -> IF k \notin i..j THEN A[k] ELSE CHOOSE x \in Permutations(A[i..j]): LET left = {x[m] : m \in 1..'pivot-i+1}, right = {x[n] : n \in 'pivot-i+2..'j-i+1} IN \A l \in left, r \in right: l <= r]
       /\ S' = (S \ {<<i, j>>}) \cup {<<i, pivot-1>>, <<pivot+1, j>>}
       /\ pc' = "Start"
    \/ /\ pc = "Start"
       /\ S /= {}
       /\ <<i, j>> \in S
       /\ i = j
       /\ A' = A
       /\ S' = S \ {<<i, j>>}
       /\ pc' = "Start"
    \/ /\ pc = "Start"
       /\ S = {}
       /\ A' = A
       /\ S' = S
       /\ pc' = "Done"

Spec == Init /\ [][Next]_<<Ainit, A, S, pivot, pc>> \/ <>(pc = "Done")

=============================================================================