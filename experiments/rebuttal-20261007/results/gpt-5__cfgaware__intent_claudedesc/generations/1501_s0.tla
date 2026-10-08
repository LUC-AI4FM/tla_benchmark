---- MODULE RecursiveFactDemo ----
EXTENDS Naturals

VARIABLES v

RECURSIVE Fact(_)

Fact(n) ==
  IF n = 0 THEN 1 ELSE n * Fact(n - 1)

Init ==
  v = 0

Next ==
  \/ v' = Fact(3)
  \/ v' = Fact(5)

Spec ==
  Init /\ [][Next]_v
====