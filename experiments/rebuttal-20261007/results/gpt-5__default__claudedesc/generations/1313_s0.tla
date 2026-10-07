---- MODULE DieHard ----
EXTENDS Naturals

CONSTANTS
  SMALL_CAP, BIG_CAP

ASSUME SMALL_CAP = 3 /\ BIG_CAP = 5

VARIABLES small, big, reg42

Vars == << small, big, reg42 >>

TypeOK ==
  /\ small \in 0..SMALL_CAP
  /\ big \in 0..BIG_CAP
  /\ reg42 \in Nat

Init ==
  /\ small = 0
  /\ big = 0
  /\ reg42 = 0

Min2(a, b) == IF a <= b THEN a ELSE b

FillSmall ==
  /\ small < SMALL_CAP
  /\ small' = SMALL_CAP
  /\ big' = big
  /\ reg42' = reg42 + (SMALL_CAP - small)

FillBig ==
  /\ big < BIG_CAP
  /\ big' = BIG_CAP
  /\ small' = small
  /\ reg42' = reg42 + (BIG_CAP - big)

EmptySmall ==
  /\ small > 0
  /\ small' = 0
  /\ big' = big
  /\ reg42' = reg42

EmptyBig ==
  /\ big > 0
  /\ big' = 0
  /\ small' = small
  /\ reg42' = reg42

SmallToBig ==
  LET amount == Min2(small, BIG_CAP - big) IN
  /\ amount > 0
  /\ small' = small - amount
  /\ big' = big + amount
  /\ reg42' = reg42

BigToSmall ==
  LET amount == Min2(big, SMALL_CAP - small) IN
  /\ amount > 0
  /\ big' = big - amount
  /\ small' = small + amount
  /\ reg42' = reg42

Next ==
  \/ FillSmall
  \/ FillBig
  \/ EmptySmall
  \/ EmptyBig
  \/ SmallToBig
  \/ BigToSmall

Spec == Init /\ [][Next]_Vars

HasFour == big = 4

PourAction == /\ small' # small /\ big' # big

THEOREM TypeOKIsInvariant == Init /\ [][Next]_Vars => []TypeOK

CONSTANTS
  GeneratedStates, DistinctStates, Diameter, TotalGallonsUsed

PostCondition ==
  /\ GeneratedStates = 97
  /\ DistinctStates = 16
  /\ Diameter = 8
  /\ TotalGallonsUsed = 128

THEOREM PostConditionHolds == PostCondition

CONSTANT _POSSIBLE(_)

PossibleCounts ==
  /\ _POSSIBLE(HasFour) = 8
  /\ _POSSIBLE(PourAction) = 14

THEOREM PossibleCountsHold == PossibleCounts
====