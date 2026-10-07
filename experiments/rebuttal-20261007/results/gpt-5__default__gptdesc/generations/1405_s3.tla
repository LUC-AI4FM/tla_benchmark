------------------------------ MODULE Outer ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS S0
ASSUME S0 \in Seq(Nat)

VARIABLES r, s

I == INSTANCE Inner WITH res <- r, seq <- s

Init == /\ r = 0
        /\ s = S0

StepEnabled == ENABLED I!Step

Next == I!Step
        \/ /\ ~StepEnabled
           /\ UNCHANGED <<r, s>>

Spec == Init /\ [][Next]_<<r, s>> /\ WF_<<r, s>>(I!Step)

Live == <>[] ~ENABLED I!Step

THEOREM Spec => Live
=============================================================================