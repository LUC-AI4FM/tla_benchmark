------------------------------- MODULE GCDLoop -------------------------------

CONSTANTS pc, u, v, vars

VARIABLES pc, u, v

Init == 
    /\ pc = "start"
    /\ u = 24
    /\ v \in 1..50

StepStart ==
    \/ /\ pc = "start"
       /\ u < v
       /\ pc' = "swap"
       /\ u' = v
       /\ v' = u
    \/ /\ pc = "start"
       /\ u >= v
       /\ pc' = "subtract"
       /\ u' = u - v
       /\ v' = v

StepSwap ==
    \/ /\ pc = "swap"
       /\ u < v
       /\ pc' = "swap"
       /\ u' = v
       /\ v' = u
    \/ /\ pc = "swap"
       /\ u >= v
       /\ pc' = "subtract"
       /\ u' = u - v
       /\ v' = v

StepSubtract ==
    \/ /\ pc = "subtract"
       /\ u > 0
       /\ pc' = "start"
       /\ u' = u - v
       /\ v' = v
    \/ /\ pc = "subtract"
       /\ u = 0
       /\ pc' = "done"

Next == 
    StepStart \/ StepSwap \/ StepSubtract

Spec == 
    /\ Init
    /\ [][Next]_<<pc, u, v>>

=============================================================================