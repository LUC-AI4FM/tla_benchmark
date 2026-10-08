----------------------------- MODULE ConjInitSimultaneous -----------------------------

EXTENDS Integers, TLC

(*
Demonstrates that conjunctive initial-state predicates are solved simultaneously.
The only reachable state is x = 0 /\ y = 0, and the system stutters forever.
*)

VARIABLES x, y

vars == << x, y >>

Init ==
  /\ y = 0
  /\ x = 0
  /\ y = x

Next ==
  /\ x' = x
  /\ y' = y

Spec == Init /\ [][Next]_vars

TypeOK == /\ x \in Int /\ y \in Int
Inv == /\ x = 0 /\ y = 0

=============================================================================