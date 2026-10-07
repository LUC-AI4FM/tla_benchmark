----------------------------- MODULE Modulo3 -----------------------------
EXTENDS Naturals, TLC

VARIABLES x

Init ==
  x = 0

(*
  Helper predicates with labels for TLC coverage:
  - StateIs1: state predicate true exactly when x = 1
  - Done: state predicate true exactly when x = 2
  - Wrap: action predicate true exactly on the 2 -> 0 transition
*)
StateIs1 == StateIs1Lbl :: x = 1
Done     == DoneLbl     :: x = 2
Wrap     == WrapLbl     :: /\ x = 2 /\ x' = 0

(*
  Transition relation: advance modulo 3
*)
Step01 == /\ x = 0 /\ x' = 1
Step12 == /\ x = 1 /\ x' = 2
Step20 == Wrap

Next ==
  Step01 \/ Step12 \/ Step20

(*
  Safety invariant: x remains in {0,1,2}
*)
TypeInv == x \in 0..2

(*
  Probe ensures StateIs1 and Done are evaluated in every state (without
  constraining behaviors), so their labels are visible to TLC coverage.
*)
Probe ==
  /\ IF StateIs1 THEN TRUE ELSE TRUE
  /\ IF Done     THEN TRUE ELSE TRUE

Spec ==
  Init /\ [][Next]_x /\ []Probe

Safety ==
  []TypeInv

(*
  TLC-specific coverage check:
  Inspects TLC's coverage data and asserts each named predicate
  (StateIs1Lbl, DoneLbl, WrapLbl) is counted once.
  Note: This operator is provided for TLC use and is not part of Spec.
*)
CoverageCheck ==
  LET cov == TLCGet("coverage")
  IN /\ Assert(cov["StateIs1Lbl"] = 1, "Expected coverage count 1 for StateIs1Lbl")
     /\ Assert(cov["DoneLbl"]     = 1, "Expected coverage count 1 for DoneLbl")
     /\ Assert(cov["WrapLbl"]     = 1, "Expected coverage count 1 for WrapLbl")

============================================================================