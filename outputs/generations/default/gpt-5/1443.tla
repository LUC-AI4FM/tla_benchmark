----------------------------- MODULE Modulo3 -----------------------------
EXTENDS Naturals, TLC

VARIABLES x

vars == << x >>

Init == x = 0

IsOne == x = 1
Done  == x = 2
Wrap  == x = 2 /\ x' = 0

Next ==
  \/ /\ x # 2 /\ x' = x + 1
  \/ /\ Wrap

TypeOK == x \in {0, 1, 2}

Inv == TypeOK

Spec == Init /\ [][Next]_vars

Safety == []Inv

CoverageCheck ==
  LET cov == TLCGet("coverage") IN
    /\ Assert(cov["IsOne"] = 1, "Coverage for IsOne not 1")
    /\ Assert(cov["Done"]  = 1, "Coverage for Done not 1")
    /\ Assert(cov["Wrap"]  = 1, "Coverage for Wrap not 1")
============================================================================