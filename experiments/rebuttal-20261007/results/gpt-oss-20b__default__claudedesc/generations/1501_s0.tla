MODULE D
EXTENDS Naturals

VARIABLE x

RECURSIVE fact/1

fact(n) ==
  IF n = 1 THEN 1 ELSE n * fact(n - 1)

Init == x = 0

A == x' = fact(3)
B == x' = fact(9)

Next == A \/ B

Spec == Init /\ [] [ Next ]_x