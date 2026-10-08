------------------------------ MODULE ConstrainedEvenVar ------------------------------

EXTENDS Integers, Naturals

CONSTANTS Allowed

ASSUME Allowed = { n \in 0..9 : \E k \in Nat : n = 2 * k }

VARIABLES x

Init == x = 0

Next == x' \in Allowed

Spec == Init /\ [][Next]_x

=============================================================================