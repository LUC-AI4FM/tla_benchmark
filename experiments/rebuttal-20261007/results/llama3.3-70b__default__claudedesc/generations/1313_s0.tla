```tla
MODULE DieHardWaterJugPuzzle

EXTENDS Integers

CONSTANTS FillSmall, FillBig, EmptySmall, EmptyBig, SmallToBig, BigToSmall

VARIABLES small, big, counter

Init ==
  /\ small = 0
  /\ big = 0
  /\ counter = 0

Next ==
  \/ (FillSmall = TRUE /\ small' = 3 /\ big' = big /\ counter' = counter + 3)
  \/ (FillBig = TRUE /\ small' = small /\ big' = 5 /\ counter' = counter + 5)
  \/ (EmptySmall = TRUE /\ small' = 0 /\ big' = big /\ counter' = counter)
  \/ (EmptyBig = TRUE /\ small' = small /\ big' = 0 /\ counter' = counter)
  \/ (SmallToBig = TRUE /\ small' = 0 /\ big' = Min(big + small, 5) /\ counter' = counter)
  \/ (BigToSmall = TRUE /\ small' = Min(small + big, 3) /\ big' = 0 /\ counter' = counter)

TypeOK ==
  /\ small \in 0..3
  /\ big \in 0..5

HasFour ==
  big = 4

PourAction ==
  (SmallToBig = TRUE \/ BigToSmall = TRUE)

Spec ==
  Init /\ [][Next]_<<small, big, counter>>

PostCondition ==
  /\ TLC.StateCount = 97
  /\ TLC.DistinctStateCount = 16
  /\ TLC.Diameter = 8
  /\ counter = 128

PossibleCounts ==
  /\ [_POSSIBLE HasFour]_small = 8
  /\ [_POSSIBLE PourAction]_small = 14

THEOREM Spec => []PostCondition
```