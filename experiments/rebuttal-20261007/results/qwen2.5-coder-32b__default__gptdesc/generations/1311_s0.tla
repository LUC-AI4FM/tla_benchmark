------------------------------- MODULE GCDLoop -------------------------------
EXTENDS Naturals, TLC

CONSTANTS v_init \* v is chosen from 1 .. 50

VARIABLES u, v, pc

Init == 
    /\ u = 24
    /\ v = v_init
    /\ pc = "start"

Next ==
    \/ /\ pc = "start"
       /\ v > 0
       /\ v <= 50
       /\ pc' = "loop"
    \/ /\ pc = "loop"
       /\ u < v
       /\ u' = v
       /\ v' = u
       /\ pc' = "loop"
    \/ /\ pc = "loop"
       /\ u >= v
       /\ u' = u - v
       /\ v' = v
       /\ pc' = "loop"
    \/ /\ pc = "loop"
       /\ u = 0
       /\ pc' = "done"
    \/ /\ pc = "done"
       /\ UNCHANGED <<u, v>>
       /\ pc' = pc

Spec ==
    /\ Init
    /\ [][Next]_<<u, v, pc>>

\* Fairness conditions
WF_vars == WF_next(<<u, v, pc>>, Next)

Termination ==
    <>[](pc = "done")

=============================================================================