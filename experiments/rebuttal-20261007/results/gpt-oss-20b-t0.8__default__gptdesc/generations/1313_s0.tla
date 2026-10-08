MODULE DieHardWaterJug
EXTENDS Naturals, Sequences

CONSTANT SmallCap, BigCap
SmallCap == 3
BigCap == 5

VARIABLES small, big, waterUsed, stateCount

Init ==
  /\ small = 0
  /\ big = 0
  /\ waterUsed = 0
  /\ stateCount = 1

FillSmall ==
  /\ small < SmallCap
  /\ small' = SmallCap
  /\ big' = big
  /\ waterUsed' = waterUsed + (SmallCap - small)
  /\ stateCount' = stateCount + 1

EmptySmall ==
  /\ small > 0
  /\ small' = 0
  /\ big' = big
  /\ waterUsed' = waterUsed
  /\ stateCount' = stateCount + 1

FillBig ==
  /\ big < BigCap
  /\ big' = BigCap
  /\ small' = small
  /\ waterUsed' = waterUsed + (BigCap - big)
  /\ stateCount' = stateCount + 1

EmptyBig ==
  /\ big > 0
  /\ big' = 0
  /\ small' = small
  /\ waterUsed' = waterUsed
  /\ stateCount' = stateCount + 1

PourSmallToBig ==
  /\ small > 0
  /\ big < BigCap
  /\ LET amount == IF small <= (BigCap - big) THEN small ELSE (BigCap - big)
     IN
    /\ small' = small - amount
    /\ big' = big + amount
    /\ waterUsed' = waterUsed + amount
    /\ stateCount' = stateCount + 1

PourBigToSmall ==
  /\ big > 0
  /\ small < SmallCap
  /\ LET amount == IF big <= (SmallCap - small) THEN big ELSE (SmallCap - small)
     IN
    /\ big' = big - amount
    /\ small' = small + amount
    /\ waterUsed' = waterUsed + amount
    /\ stateCount' = stateCount + 1

Stutter ==
  /\ small' = small
  /\ big' = big
  /\ waterUsed' = waterUsed
  /\ stateCount' = stateCount

Next ==
  \/ FillSmall
  \/ EmptySmall
  \/ FillBig
  \/ EmptyBig
  \/ PourSmallToBig
  \/ PourBigToSmall
  \/ Stutter

Variables == <<small, big, waterUsed, stateCount>>

Spec ==
  Init /\ [][Next]_Variables

SafetyInvariant ==
  /\ small >= 0
  /\ small <= SmallCap
  /\ big >= 0
  /\ big <= BigCap
  /\ waterUsed >= 0
  /\ stateCount >= 1

THEOREM Safety : Spec => [] SafetyInvariant

LivenessGoal ==
  <> (big = 4)

THEOREM ReachBigFour : Spec => LivenessGoal

END MODULE