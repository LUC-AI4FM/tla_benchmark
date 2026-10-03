------------------------------- MODULE spec -------------------------------

EXTENDS Integers, Naturals

VARIABLES u, v, pc

vars == <<u, v, pc>>

Init == 
    /\ u = 24
    /\ v \in 1..50
    /\ pc = "start"

start == 
    /\ pc = "start"
    /\ IF u < v
       THEN /\ u' = v
            /\ v' = u
            /\ pc' = "start"
       ELSE IF u # 0
            THEN /\ u' = u - v
                 /\ v' = v
                 /\ pc' = "start"
            ELSE /\ pc' = "Done"
                 /\ u' = u
                 /\ v' = v

Done == 
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == 
    \/ start
    \/ Done

Spec == Init /\ [][Next]_vars

=============================================================================