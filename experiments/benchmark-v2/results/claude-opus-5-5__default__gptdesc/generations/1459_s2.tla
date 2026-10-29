---------------------------- MODULE SmallCounter ----------------------------
EXTENDS Naturals

VARIABLES x

vars == << x >>

Init == x = 0

Increment == /\ x < 3
             /\ x' = x + 1

Stutter == /\ x >= 3
           /\ UNCHANGED x

Next == Increment \/ Stutter

Spec == Init /\ [][Next]_x

-----------------------------------------------------------------------------
(* Safety invariants *)

TypeOK == x \in Nat

Bounded == x \in 0..3

=============================================================================