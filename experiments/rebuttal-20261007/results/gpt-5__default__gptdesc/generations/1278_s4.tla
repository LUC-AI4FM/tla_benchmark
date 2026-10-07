------------------------------ MODULE EvenDigitSpec ------------------------------

EXTENDS Naturals, Integers

CONSTANTS Dummy

VARIABLES s

F(x) == x \in 0..9 /\ \E k \in Nat : x = 2 * k

Init == s = 0

Next == F(s')

Spec == Init /\ [] [Next]_s

=============================================================================