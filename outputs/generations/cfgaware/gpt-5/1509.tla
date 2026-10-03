------------------------------ MODULE TinyRecursionSystem ------------------------------

EXTENDS Integers

VARIABLE x

S == {1,2,3,4,5}
K == {1,2,3}

RECURSIVE F(_)
F(n) ==
  IF n = 1 THEN 1
  ELSE IF n \in {2,3,4,5} THEN F(n - 1) + n
  ELSE 0

N(i) ==
  /\ i \in K
  /\ x' = x + i

Init == x = F(1)

Spec == Init /\ [] [ \E i \in K: N(i) ]_x

Inv == \E n \in S: x >= F(n)

==============================