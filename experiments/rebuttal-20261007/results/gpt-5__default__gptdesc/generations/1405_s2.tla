------------------------------ MODULE Outer ------------------------------
EXTENDS Naturals, Sequences

VARIABLES r, s

vars == <<r, s>>

M == INSTANCE Inner WITH res <- r, seq <- s

Init == M!Init

Next == M!Step \/ (~ENABLED M!Step /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars /\ WF_vars(M!Step)

Liveness == <>[] ~ENABLED M!Step

THEOREM Spec => Liveness
=============================================================================