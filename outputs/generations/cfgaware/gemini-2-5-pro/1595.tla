---- MODULE FairCounter ----
EXTENDS Integers, TLC

VARIABLES x, pc

vars == <<x, pc>>

Init ==
    /\ x = 0
    /\ pc = "Loop"

Increment ==
    /\ pc = "Loop"
    /\ x < 10
    /\ x' = x + 1
    /\ pc' = "Loop"

TerminateLoop ==
    /\ pc = "Loop"
    /\ x >= 10
    /\ pc' = "Done"
    /\ x' = x

Next ==
    \/ Increment
    \/ TerminateLoop

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

AtFive == x = 5

FinishLoop == pc = "Done"

PossibleCounts ==
    LET stats == TLCGet("stats")
    IN  /\ stats.atFive = 1
        /\ stats.finishLoop = 1

=============================================================================