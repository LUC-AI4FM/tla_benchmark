---------------------------- MODULE ModIncrement ----------------------------
(* Test of parametrized INSTANCE *)
EXTENDS Naturals

VARIABLES x

Init == x = 0

Next == x' = (x + 1) % 5

Spec == Init /\ [][Next]_x

TypeOK == x \in 0..4

=============================================================================