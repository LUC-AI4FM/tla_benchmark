---------------------------- MODULE Counter ----------------------------
EXTENDS Naturals, TLC

CONSTANTS DUMMY

VARIABLES x, pc, cFive, cFinish

vars == << x, pc, cFive, cFinish >>

AtFive == x = 5
FinishLoop == x = 9
FinishLoopAct == (x = 9) /\ (x' = 10)

TypeOK == /\ x \in Int
          /\ pc \in {"Lbl_1", "Done"}
          /\ cFive \in Nat
          /\ cFinish \in Nat

Bounded == /\ 0 <= x
           /\ x <= 10

PossibleCounts == /\ cFive = 1
                  /\ cFinish = 1

Init ==
    /\ x = 0
    /\ pc = "Lbl_1"
    /\ cFive = 0
    /\ cFinish = 0
    /\ TLCSet("exit", PossibleCounts)

Lbl_1 ==
    /\ pc = "Lbl_1"
    /\ IF x < 10
          THEN /\ x' = x + 1
               /\ pc' = "Lbl_1"
          ELSE /\ x' = x
               /\ pc' = "Done"
    /\ cFive' = cFive + IF x' = 5 THEN 1 ELSE 0
    /\ cFinish' = cFinish + IF (x = 9 /\ x' = 10) THEN 1 ELSE 0

Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == Lbl_1 \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <> (pc = "Done")
=======================================================================