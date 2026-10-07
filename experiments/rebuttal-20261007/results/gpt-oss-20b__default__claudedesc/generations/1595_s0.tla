------------------------------ MODULE Counter ------------------------------
EXTENDS Integers, TLC

VARIABLES x, pc

vars == <<x, pc>>

Init ==
  /\ x = 0
  /\ pc = "Lbl_1"

Lbl_1 ==
  /\ pc = "Lbl_1"
  /\ x < 10
  /\ x' = x + 1
  /\ pc' = IF x + 1 = 10 THEN "Done" ELSE "Lbl_1"

Terminating ==
  /\ pc = "Done"
  /\ UNCHANGED <<x, pc>>

Next == Lbl_1 \/ Terminating

Spec == Init /\ [] [Next]_vars /\ WF_1(Next)

Termination == <> (pc = "Done")

\*_POSSIBLE AtFive == x = 5
\*_POSSIBLE FinishLoop == x = 9

PossibleCounts ==
  \A p \in {AtFive, FinishLoop} : TLCStateCount(p) = 1

=============================================================================