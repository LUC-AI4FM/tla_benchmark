------------------------------ MODULE DieHard ------------------------------

EXTENDS Naturals, TLC

CONSTANTS SmallCap, BigCap

ASSUME SmallCap = 3 /\ BigCap = 5

VARIABLES s, b, w

vars == << s, b, w >>

Delta(x, y) == IF x >= y THEN x - y ELSE y - x

UpdateWaterUsage == w' = w + Delta(s' + b', s + b)

Init ==
  /\ s = 0
  /\ b = 0
  /\ w = 0

FillSmall ==
  /\ s < SmallCap
  /\ s' = SmallCap
  /\ b' = b
  /\ UpdateWaterUsage

FillBig ==
  /\ b < BigCap
  /\ b' = BigCap
  /\ s' = s
  /\ UpdateWaterUsage

EmptySmall ==
  /\ s > 0
  /\ s' = 0
  /\ b' = b
  /\ UpdateWaterUsage

EmptyBig ==
  /\ b > 0
  /\ b' = 0
  /\ s' = s
  /\ UpdateWaterUsage

PourSmallToBig ==
  /\ s > 0
  /\ b < BigCap
  /\ LET amt == IF s <= BigCap - b THEN s ELSE BigCap - b
     IN /\ s' = s - amt
        /\ b' = b + amt
  /\ UpdateWaterUsage

PourBigToSmall ==
  /\ b > 0
  /\ s < SmallCap
  /\ LET amt == IF b <= SmallCap - s THEN b ELSE SmallCap - s
     IN /\ b' = b - amt
        /\ s' = s + amt
  /\ UpdateWaterUsage

Next ==
  \/ FillSmall
  \/ FillBig
  \/ EmptySmall
  \/ EmptyBig
  \/ PourSmallToBig
  \/ PourBigToSmall

Spec == Init /\ [][Next]_vars

TypeInv ==
  /\ s \in 0..SmallCap
  /\ b \in 0..BigCap
  /\ w \in Nat

ConservationInv ==
  /\ 0 <= s + b
  /\ s + b <= SmallCap + BigCap

SafetyInv == TypeInv /\ ConservationInv

Goal == <> (b = 4)

MCNumStates == TLCGet("numStates")
MCNumActions == TLCGet("numActions")

CountsOK ==
  /\ MCNumStates \in Nat
  /\ MCNumStates >= 1
  /\ MCNumActions \in Nat
  /\ MCNumActions >= 1

============================================================================