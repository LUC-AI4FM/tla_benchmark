-------------------------- MODULE SmallRecSpec --------------------------

EXTENDS Integers

CONSTANTS Dummy

VARIABLES x

S == 1..5
I == 1..3

RECURSIVE F(_)
F(n) ==
  IF n = 1 THEN 1
  ELSE IF n \in S THEN F(n - 1) + n
  ELSE 0

Init == x = 0

N(i) ==
  /\ i \in I
  /\ x' = x + i
  /\ x' <= F(5)

Next == \E i \in I : N(i)

Inv == x \in 0..F(5)

Spec == Init /\ [] [Next]_x

============================================================================