------------------------------- MODULE TinyXY -------------------------------
EXTENDS TLC

CONSTANTS
  EXPECTED_FullSet,
  EXPECTED_GainThree

VARIABLES x, y

Vars == <<x, y>>

Init ==
  /\ x \in SUBSET {1, 2, 3}
  /\ y \in SUBSET {1, 2, 3}

Next ==
  /\ y' = y
  /\ x' \in SUBSET y'

FullSet ==
  x = {1, 2, 3}

GainThree ==
  /\ ~(3 \in x)
  /\   3 \in x'

TypeInv ==
  /\ x \in SUBSET {1, 2, 3}
  /\ y \in SUBSET {1, 2, 3}

Coverage == TLCGet("coverage")

FullSetCount == Coverage["FullSet"]

GainThreeCount == Coverage["GainThree"]

CountsOk ==
  /\ Assert(FullSetCount = EXPECTED_FullSet, "FullSet count mismatch")
  /\ Assert(GainThreeCount = EXPECTED_GainThree, "GainThree count mismatch")

Spec ==
  Init /\ [][Next]_Vars
=============================================================================