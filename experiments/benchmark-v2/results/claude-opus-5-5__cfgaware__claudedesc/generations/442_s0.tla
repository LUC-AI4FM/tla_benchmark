--------------- MODULE test56 -------------
EXTENDS Naturals

VARIABLE x

I == INSTANCE test56a WITH u <- x

Init == x \in 1..3

Next == x' = 9 - x

NotIBangH == (x' = x) /\ I!G(x, x')

Spec == Init /\ [][Next]_x

Property == [][I!H = NotIBangH]_x
=============================================================================