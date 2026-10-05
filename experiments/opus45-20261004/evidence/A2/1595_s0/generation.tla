---------------------------- MODULE SimpleCounter ----------------------------

EXTENDS Integers, TLC

VARIABLES x, pc

vars == << x, pc >>

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
    /\ TLCGet("spec")["AtFive_POSSIBLE"] = 1
    /\ TLCGet("spec")["FinishLoop_POSSIBLE"] = 1

TypeInvariant ==
    /\ x \in 0..10
    /\ pc \in {"Lbl_1", "Done"}

SafetyInvariant ==
    /\ x >= 0
    /\ x <= 10

=============================================================================