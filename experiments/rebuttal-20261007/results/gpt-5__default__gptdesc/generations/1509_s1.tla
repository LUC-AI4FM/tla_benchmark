----------------------------- MODULE TinyRecSpec -----------------------------

EXTENDS Naturals, Integers

CONSTANTS S, I

ASSUME S = {1, 2, 3, 4, 5} /\ I = {1, 2, 3}

VARIABLES x

RECURSIVE F(_)

F(n) ==
  IF n = 1 THEN 1
  ELSE F(n - 1) + 1

N(i) ==
  /\ i \in I
  /\ \E n \in S:
        /\ x = F(n)
        /\ LET sum == n + i IN
             x' = F(IF sum <= 5 THEN sum ELSE sum - 5)

Init ==
  x \in { F(n) : n \in S }

Next ==
  \E i \in I: N(i)

Spec ==
  Init /\ [] [Next]_x

Inv ==
  \E n \in S: x = F(n)

=============================================================================