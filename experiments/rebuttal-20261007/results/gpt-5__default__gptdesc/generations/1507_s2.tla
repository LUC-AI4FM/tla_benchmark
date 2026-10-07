----------------------------- MODULE TinyBooleanClock -----------------------------

EXTENDS Naturals

(*
  This module models a tiny one-variable system with a single Boolean state variable `clock`.
  It defines two recursive operators, `Check` and `Flip`, used to express:
    - a type predicate (TypeOK),
    - an initial-state predicate (Init), and
    - a separate constraint-like state predicate (StateConstraint).

  Note: The recursive operator call Flip(FALSE, FlipInitDepth) appears in Init.
  TLC’s coverage reports may attribute exploration to the body of Flip rather than the call site.
*)

CONSTANTS FlipInitDepth, TypeDepth, ConstrDepth

(*
  For concrete usage with TLC, one can either assign these constants in a configuration
  or keep the following assumptions to fix representative depths.
*)
ASSUME /\ FlipInitDepth = 1
       /\ TypeDepth     = 1
       /\ ConstrDepth   = 2

VARIABLES clock

RECURSIVE Check(_, _)
RECURSIVE Flip(_, _)

(*
  Flip(b, n) flips the Boolean value b exactly n times.
*)
Flip(b, n) ==
  IF n = 0 THEN b ELSE Flip(~b, n - 1)

(*
  Check(b, n) asserts that b is a Boolean and, n times, recursively checks the Boolean-ness
  of alternating flips of b.
*)
Check(b, n) ==
  IF n = 0
    THEN b \in BOOLEAN
    ELSE /\ b \in BOOLEAN
         /\ Check(~b, n - 1)

(*
  Type predicate using the recursive Check operator.
*)
TypeOK == Check(clock, TypeDepth)

(*
  A separate constraint-like state predicate using the recursive Flip operator.
  Flipping a Boolean twice yields the original value.
*)
StateConstraint == Flip(clock, ConstrDepth) = clock

(*
  Initial state uses the recursive Flip operator to define the starting value of `clock`,
  and also enforces the recursive type predicate.
*)
Init ==
  /\ TypeOK
  /\ clock = Flip(FALSE, FlipInitDepth)

(*
  Transition: flip the Boolean value of `clock`.
*)
Next ==
  clock' = ~clock

vars == << clock >>

(*
  System behavior: initial states, then repeatedly take Next-steps; additionally,
  require the constraint-like state predicate to hold in every state.
*)
Spec ==
  /\ Init
  /\ []StateConstraint
  /\ [][Next]_vars

=============================================================================