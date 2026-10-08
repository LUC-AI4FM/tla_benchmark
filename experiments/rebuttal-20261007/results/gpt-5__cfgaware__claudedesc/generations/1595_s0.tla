---- MODULE Counter ----
EXTENDS Integers

VARIABLES x, pc

vars == << x, pc >>

Init ==
  /\ x = 0
  /\ pc = "Lbl_1"

TypeOK ==
  /\ x \in 0..10
  /\ pc \in {"Lbl_1", "Done"}

Lbl_1 ==
  /\ pc = "Lbl_1"
  /\ x < 10
  /\ x' = x + 1
  /\ pc' = IF x' = 10 THEN "Done" ELSE "Lbl_1"

Terminating ==
  /\ pc = "Done"
  /\ x' = x
  /\ pc' = "Done"

Next == Lbl_1 \/ Terminating

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)

Termination == <> (pc = "Done")

AtFive == x = 5

FinishLoop == /\ pc = "Lbl_1" /\ x = 9

UniqueOnce(P) == (<> P) /\ ([] (P => [] ~P))

PossibleCounts == UniqueOnce(AtFive) /\ UniqueOnce(FinishLoop)
====