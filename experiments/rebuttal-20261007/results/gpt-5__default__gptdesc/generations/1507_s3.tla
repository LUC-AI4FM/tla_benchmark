----------------------------- MODULE TinyClock -----------------------------
EXTENDS Naturals

(*
This specification models a tiny one-variable system with a single state
variable clock over Boolean values. It defines two recursive operators,
Check and Flip, and uses them to express a type predicate, an initial-state
predicate, and a separate constraint-like state predicate. The behavior
consists of a transition that flips the Boolean value of clock.

Note: TLC coverage reports may not mark recursive operator calls that appear
only inside Init as covered, even though they are evaluated.
*)

CONSTANTS DummyConstant

VARIABLES clock

vars == << clock >>

RECURSIVE Check(_,_)
Check(n, v) ==
  IF n = 0 THEN v ELSE Check(n - 1, v)

RECURSIVE Flip(_,_)
Flip(n, v) ==
  IF n = 0 THEN v ELSE Flip(n - 1, ~v)

TypeOK == Check(1, clock) \in BOOLEAN

Constraint == Flip(2, clock) = clock

Init ==
  /\ clock = Check(2, FALSE)
  /\ TypeOK
  /\ Constraint

Next ==
  /\ clock' = Flip(1, clock)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ []TypeOK
  /\ []Constraint
============================================================================