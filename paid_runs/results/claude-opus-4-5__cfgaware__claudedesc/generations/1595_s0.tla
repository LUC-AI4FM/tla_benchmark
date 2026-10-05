---------------------------- MODULE counter ----------------------------
EXTENDS Integers, TLC

VARIABLES x, pc

vars == <<x, pc>>

Init ==
    /\ x = 0
    /\ pc = "Lbl_1"

Lbl_1 ==
    /\ pc = "Lbl_1"
    /\ IF x < 10
       THEN /\ x' = x + 1
            /\ pc' = "Lbl_1"
       ELSE /\ pc' = "Done"
            /\ x' = x

Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ Lbl_1
    \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

AtFive == x = 5

FinishLoop == x = 9 /\ pc = "Lbl_1"

AtFive_POSSIBLE == AtFive

FinishLoop_POSSIBLE == FinishLoop

PossibleCounts ==
    /\ TLCGet("stats").states.distinct = 12
    /\ TLCGet("spec").config.properties.AtFive_POSSIBLE.witnessed = 1
    /\ TLCGet("spec").config.properties.FinishLoop_POSSIBLE.witnessed = 1

=========================================================================