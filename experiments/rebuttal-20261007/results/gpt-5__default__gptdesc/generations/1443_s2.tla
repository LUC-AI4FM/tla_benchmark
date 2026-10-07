----------------------------- MODULE Mod3Cycle -----------------------------

EXTENDS Naturals, TLC

CONSTANTS DummyConstant

VARIABLES x

IsOne == x = 1
Done  == x = 2
Wrap  == x = 2 /\ x' = 0

Init == x = 0

Next ==
  \/ /\ x # 2
     /\ x' = x + 1
  \/ Wrap

TypeInv == x \in {0, 1, 2}

CoveragePred ==
  LET cov == TLCGet("statePredicates")
  IN /\ cov["IsOne"] = 1
     /\ cov["Done"]  = 1
     /\ cov["Wrap"]  = 1

CoverageCheck ==
  Assert(CoveragePred, "Expected named predicate coverage (IsOne, Done, Wrap) to be exactly 1 each.")

Spec == Init /\ [][Next]_x

============================================================================