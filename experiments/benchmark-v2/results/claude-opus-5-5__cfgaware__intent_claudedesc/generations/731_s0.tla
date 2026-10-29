---------------------------- MODULE BoundedCounter ----------------------------
EXTENDS Naturals, TLC

CONSTANT UpperBound

ASSUME UpperBoundIsNat == UpperBound \in Nat

ASSUME PrintT("BoundedCounter: starting model check")

VARIABLE x

vars == << x >>

TypeOK == x \in Nat

Init == x = 0

Next == x' = x + 1

Spec == Init /\ [][Next]_vars

Constraint == x < UpperBound

Invariant == x < UpperBound

=============================================================================