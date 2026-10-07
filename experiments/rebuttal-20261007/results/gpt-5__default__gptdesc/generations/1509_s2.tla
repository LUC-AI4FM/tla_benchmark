----------------------------- MODULE SmallSystem -----------------------------
EXTENDS Naturals

CONSTANTS S, Idx
ASSUME S = 1..5 /\ Idx = 1..3

VARIABLES x

RECURSIVE F(_)
F(n) ==
  IF n = 1 THEN 1
  ELSE IF n \in S THEN F(n - 1) + n
  ELSE 0

Init == \E n \in S: x = F(n)

N(i) == /\ i \in Idx
        /\ x' = F(i)

A == \E i \in Idx: N(i)

Next == A

Spec == Init /\ [] [A]_x

Inv == x \in { F(n) : n \in S }

=============================================================================