---- MODULE TinyBooleanClock ----
EXTENDS TLC

(*
  A tiny one-variable system with a single Boolean state variable `clock`.
  Two recursive operators, `Check` and `Flip`, are used to express:
    - a type predicate (TypeOK),
    - an initial-state predicate (Init),
    - and a separate constraint-like state predicate (StateConstraint).
  Behavior: a transition that flips the Boolean value of `clock`.
*)

CONSTANTS Dummy

VARIABLES clock

(*
  Declare recursive operators.
*)
RECURSIVE Check(_), Flip(_)

(*
  Check returns TRUE iff its argument is a Boolean. It recurses only
  on non-Boolean inputs (which never occurs here).
*)
Check(x) ==
  IF x \in BOOLEAN THEN TRUE ELSE Check(x)

(*
  Flip negates a Boolean input. It recurses only on non-Boolean inputs
  (which never occurs here).
*)
Flip(x) ==
  IF x \in BOOLEAN THEN (IF x THEN FALSE ELSE TRUE) ELSE Flip(x)

(*
  Type predicate over the state.
*)
TypeOK == Check(clock)

(*
  A separate constraint-like state predicate.
*)
StateConstraint == Check(clock)

(*
  Initial-state predicate uses the recursive operators. The Check call here
  takes the non-recursive branch, so TLC coverage may not count a visit to
  the recursive body.
*)
Init ==
  /\ clock = Flip(FALSE)
  /\ Check(clock)

(*
  Transition flips the Boolean value of `clock`.
*)
Next ==
  clock' = Flip(clock)

(*
  System specification. Includes a constraint-like always-state predicate.
*)
Spec ==
  /\ Init
  /\ [][Next]_<<clock>>
  /\ []StateConstraint

(*
  A simple safety invariant stating the variable’s type explicitly.
*)
ClockIsBoolean == clock \in BOOLEAN

====