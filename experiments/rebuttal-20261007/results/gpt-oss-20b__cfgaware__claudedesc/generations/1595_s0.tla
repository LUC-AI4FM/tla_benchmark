------------------------------ MODULE Counter ------------------------------
EXTENDS Naturals, Sequences

IMPORTING TLC

VARIABLES x, pc

vars == <<x, pc>>

(* --- Initial condition ------------------------------------------------- *)
Init == /\ x = 0
        /\ pc = "Lbl_1"

(* --- Actions ----------------------------------------------------------- *)
Lbl_1 ==
  /\ pc = "Lbl_1"
  /\ x < 10
  /\ x' = x + 1
  /\ pc' = IF x' = 10 THEN "Done" ELSE "Lbl_1"

Terminate ==
  /\ pc = "Done"
  /\ x' = x
  /\ pc' = pc

Next == Lbl_1 \/ Terminate

(* --- Temporal specification ------------------------------------------- *)
Spec == Init /\ [][Next]_vars /\ WF_0(Next)

(* --- Liveness property ------------------------------------------------- *)
Termination == <> (pc = "Done")

(* --- State predicates for model‑checking --------------------------------*)
AtFive     == x = 5
FinishLoop == x = 9

(* --- Postcondition using TLC introspection ----------------------------- *)
PossibleCounts ==
  LET
      atFiveCount    == TLCStateCount(AtFive)
      finishLoopCount== TLCStateCount(FinishLoop)
  IN
      atFiveCount = 1 /\ finishLoopCount = 1

=============================================================================