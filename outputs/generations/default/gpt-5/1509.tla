----------------------------- MODULE SmallSystem -----------------------------

EXTENDS Integers

CONSTANTS S, I

ASSUME S = 1..5 /\ I = 1..3

VARIABLES x

RECURSIVE F(_)

F(n) ==
  IF n = 1 THEN 1
  ELSE IF n \in S THEN F(n - 1) + 1
  ELSE 0

N(i) ==
  /\ i \in I
  /\ x' = F(i)

Init == x = F(1)

Next == \E i \in I: N(i)

Inv == x \in { F(n) : n \in S }

Spec == Init /\ [] [Next]_x

=============================================================================