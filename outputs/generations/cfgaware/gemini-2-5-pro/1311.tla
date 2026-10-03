---- MODULE Gcd ----
EXTENDS Integers

CONSTANT U_start, V_range
VARIABLES u, v, pc

vars == <<u, v, pc>>

Init ==
    /\ u = U_start
    /\ v \in V_range
    /\ pc = "Loop"

Loop ==
    /\ pc = "Loop"
    /\ IF u > 0
       THEN IF u < v
            THEN pc' = "Swap"
            ELSE pc' = "Subtract"
       ELSE pc' = "Done"
    /\ UNCHANGED <<u, v>>

Swap ==
    /\ pc = "Swap"
    /\ u' = v
    /\ v' = u
    /\ pc' = "Subtract"

Subtract ==
    /\ pc = "Subtract"
    /\ u' = u - v
    /\ v' = v
    /\ pc' = "Loop"

Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ Loop
    \/ Swap
    \/ Subtract
    \/ Done

Spec == Init /\ [][Next]_vars

====