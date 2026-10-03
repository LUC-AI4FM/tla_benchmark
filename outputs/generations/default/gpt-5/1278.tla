------------------------------ MODULE PrimedBoxSpec ------------------------------

EXTENDS Integers

CONSTANTS Dummy

VARIABLES s

Even(n) == \E k \in Int: n = 2*k
F(x) == x \in 0..9 /\ Even(x)

Init == s = 0

Next == F(s')

Spec == Init /\ [] [F(s')]_s

SafetyInv == s \in 0..9 /\ Even(s)

=============================================================================