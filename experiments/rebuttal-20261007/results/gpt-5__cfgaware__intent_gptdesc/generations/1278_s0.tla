------------------------------ MODULE DigitEven ------------------------------

EXTENDS Naturals

VARIABLES d

IsEven(n) == \E k \in Nat: n = 2 * k

Safe == d \in 0..9 /\ IsEven(d)

Init == d = 0

Next == Safe'

vars == << d >>

Spec == Init /\ [][Next]_d

Inv == Safe

AlwaysSafe == []Safe

=============================================================================