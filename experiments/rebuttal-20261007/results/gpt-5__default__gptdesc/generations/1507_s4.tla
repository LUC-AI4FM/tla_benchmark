--------------------------- MODULE TinyClock ---------------------------

EXTENDS

CONSTANTS Dummy

VARIABLES clock

(*
  Two recursive operators used throughout:
  - Check: a recursive type-checking predicate over Booleans.
  - Flip: a recursive Boolean negation with a total definition.
*)
RECURSIVE Check(_)
Check(v) ==
  IF v \in BOOLEAN
    THEN TRUE
    ELSE Check(TRUE) /\ FALSE

RECURSIVE Flip(_)
Flip(b) ==
  IF b \in BOOLEAN
    THEN ~b
    ELSE Flip(TRUE)

(*
  Type predicate expressed via the recursive operator.
  Equivalent to clock \in BOOLEAN, but deliberately routed through Check.
*)
TypeOK == Check(clock)

(*
  A separate constraint-like state predicate; does not affect Spec unless
  used by a model checker as a state constraint.
*)
Constraint == Check(clock)

(*
  Initial state:
  - Sets clock to Flip(FALSE) = TRUE.
  - Includes a recursive call to Check; TLC coverage will attribute the
    recursive invocation appearing here when coverage is enabled.
*)
Init ==
  /\ clock = Flip(FALSE)
  /\ Check(clock)

(*
  The behavior flips the Boolean value of clock on every step.
*)
Next ==
  clock' = Flip(clock)

(*
  Safety invariant to be checked against Spec.
*)
TypeInvariant == TypeOK

(*
  Temporal specification: standard initial/step form.
*)
Spec ==
  Init /\ [][Next]_clock

===========================================================================