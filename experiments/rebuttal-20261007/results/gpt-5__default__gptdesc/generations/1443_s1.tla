----------------------------- MODULE Mod3Cycle -----------------------------

EXTENDS Naturals, TLC

VARIABLES x

(*
  Helper predicates:
  - IsOne: state predicate true exactly when x = 1
  - Done:  state predicate true exactly when x = 2 (all work considered done)
  - Wrap:  action predicate true exactly on the transition 2 -> 0
*)

IsOne == x = 1
Done  == x = 2
Wrap  == x = 2 /\ x' = 0

Init == x = 0

(*
  Next advances x modulo 3. We define it using an explicit Wrap action
  for the 2 -> 0 transition, and a non-wrap increment for 0 -> 1 and 1 -> 2.
*)
Next ==
  \/ Wrap
  \/ /\ x # 2
     /\ x' = x + 1

(*
  Safety invariant: x always ranges over {0,1,2}.
*)
TypeInv == x \in {0, 1, 2}

(*
  Temporal specification: initial condition and then steps of Next,
  allowing stuttering via the standard box-subscript form.
*)
Spec == Init /\ [][Next]_x /\ CoverageOK

(*
  TLC-specific coverage check:
  Assert, via TLCGet, that each of the three named predicates is counted once.
  This relies on TLC's coverage information for named state/action predicates.
  The exact keys are TLC-specific; this expression is evaluated by TLC.
*)
CoverageOK ==
  /\ Assert(TLCGet("coverage", "IsOne") = 1, "IsOne coverage not 1")
  /\ Assert(TLCGet("coverage", "Done")  = 1, "Done coverage not 1")
  /\ Assert(TLCGet("coverage", "Wrap")  = 1, "Wrap coverage not 1")

============================================================================