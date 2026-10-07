---------------------------- MODULE SmallRecSystem ----------------------------

EXTENDS Integers

VARIABLES x

S == 1..5
I == 1..3

RECURSIVE F(_)
F(n) ==
  IF n = 1 THEN 1
  ELSE IF n \in 2..5 THEN F(n - 1) + n
  ELSE 0

Init == x = F(1)

N(i) == /\ i \in I
        /\ x' = x + i

Next == \E i \in I : N(i)

Inv == x >= F(1)

Spec == Init /\ [] [Next]_x

=============================================================================