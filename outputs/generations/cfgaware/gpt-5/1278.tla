------------------------------ MODULE PrimedPredicateSpec ------------------------------

EXTENDS Integers

VARIABLES s

F(v) == v \in 0..9 /\ v \mod 2 = 0

Init == s = 0

Spec == Init /\ [] [F(s')]_s

============================================================================