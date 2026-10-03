---------------------------- MODULE FairCounter ----------------------------

EXTENDS Integers, TLC

VARIABLES x, pc

vars == <<x, pc>>

Init ==
    /\ x = 0
    /\ pc = "loop"

Loop ==
    /\ pc = "loop"
    /\ x < 10
    /\ x' = x + 1
    /\ pc' = "loop"

FinishLoop ==
    /\ pc = "loop"
    /\ x >= 10
    /\ pc' = "Done"
    /\ x' = x

Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ Loop
    \/ FinishLoop
    \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

AtFive == x = 5

TypeInvariant ==
    /\ x \in 0..10
    /\ pc \in {"loop", "Done"}

SafetyInvariant ==
    /\ x >= 0
    /\ x <= 10

PossibleCounts == 
    TLCGet("distinct") >= 0

=============================================================================