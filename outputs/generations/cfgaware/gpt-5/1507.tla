---- MODULE TinyClock ----
EXTENDS Naturals

(*
  A tiny one-variable system with a Boolean state variable `clock`.
  It defines two recursive operators, `Check` and `Flip`. These are used
  to express:
    - a type predicate: TypeOK
    - an initial-state predicate: Init
    - a separate constraint-like state predicate: Constraint

  Note: When running TLC with coverage, recursive calls appearing in Init
  may show limited coverage attribution to the body of `Check`, since TLC
  reports coverage at the call site.
*)

VARIABLES clock

RECURSIVE Check(_, _)
Check(n, b) ==
  IF n = 0
  THEN b \in BOOLEAN
  ELSE Check(n - 1, b)

RECURSIVE Flip(_, _)
Flip(n, b) ==
  IF n = 0
  THEN b
  ELSE Flip(n - 1, ~b)

(*
  Type predicate expressed via the recursive `Check`.
*)
TypeOK ==
  Check(2, clock)

(*
  Initial state uses `Check` and sets clock to a concrete Boolean.
*)
Init ==
  /\ Check(1, clock)
  /\ clock = FALSE

(*
  Transition flips the Boolean value of `clock` using `Flip`.
*)
Next ==
  clock' = Flip(1, clock)

(*
  A separate constraint-like state predicate that also uses the recursive operators.
  Flip(2, b) = b for Boolean b, so this holds when `clock` is Boolean.
*)
Constraint ==
  /\ Check(0, clock)
  /\ Flip(2, clock) = clock

====