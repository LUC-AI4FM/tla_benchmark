MODULE GCD
EXTENDS Naturals, Sequences, TLC

VARIABLES u, v, pc

vars == <<u,v,pc>>

Init ==
    /\ u = 24
    /\ v \in 1..50
    /\ pc = "Loop"

Swap ==
    /\ pc = "Loop"
    /\ u < v
    /\ LET tmp == u IN
       /\ u' = v
       /\ v' = tmp
       /\ pc' = "Loop"

Subtract ==
    /\ pc = "Loop"
    /\ u >= v
    /\ u > 0
    /\ u' = u - v
    /\ pc' = "Loop"

Done ==
    /\ pc = "Loop"
    /\ u = 0
    /\ pc' = "Done"
    /\ UNCHANGED <<u,v>>

StutterDone ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == Swap \/ Subtract \/ Done \/ StutterDone

Spec == Init /\ [] (Next)