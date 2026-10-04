---------------------------- MODULE specification ----------------------------

EXTENDS Integers

VARIABLES u, v, pc

vars == <<u, v, pc>>

Init ==
    /\ u = 24
    /\ v \in 1..50
    /\ pc = "start"

Swap ==
    /\ pc = "start"
    /\ u < v
    /\ u' = v
    /\ v' = u
    /\ pc' = "start"

Subtract ==
    /\ pc = "start"
    /\ u >= v
    /\ u > 0
    /\ u' = u - v
    /\ v' = v
    /\ pc' = "start"

Terminate ==
    /\ pc = "start"
    /\ u = 0
    /\ pc' = "Done"
    /\ u' = u
    /\ v' = v

Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ Swap
    \/ Subtract
    \/ Terminate
    \/ Done

Spec == Init /\ [][Next]_vars

=============================================================================