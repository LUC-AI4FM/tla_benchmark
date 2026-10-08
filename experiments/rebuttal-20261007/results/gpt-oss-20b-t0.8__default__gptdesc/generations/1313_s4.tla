```
MODULE DieHardWaterJug
EXTENDS Naturals, TLC

CONSTANTS C3, C5   \* capacities of small and big jug (expected to be 3 and 5)

VARIABLES small, big, counter, seenFour

Init == /\ small = 0
       /\ big   = 0
       /\ counter = 0
       /\ seenFour = FALSE

FillSmall ==
  /\ small'   = C3
  /\ counter' = counter + (C3 - small)
  /\ big'     = big
  /\ seenFour'= seenFour \/ (big' = 4)

EmptySmall ==
  /\ small'   = 0
  /\ big'     = big
  /\ counter' = counter
  /\ seenFour'= seenFour

PourSmallToBig ==
  LET transfer == IF small <= C5 - big THEN small ELSE C5 - big IN
    /\ small'   = small - transfer
    /\ big'     = big + transfer
    /\ counter' = counter
    /\ seenFour'= seenFour \/ (big' = 4)

FillBig ==
  /\ big'     = C5
  /\ counter' = counter + (C5 - big)
  /\ small'   = small
  /\ seenFour'= seenFour \/ (big' = 4)

EmptyBig ==
  /\ big'     = 0
  /\ small'   = small
  /\ counter' = counter
  /\ seenFour'= seenFour

PourBigToSmall ==
  LET transfer == IF big <= C3 - small THEN big ELSE C3 - small IN
    /\ big'      = big - transfer
    /\ small'    = small + transfer
    /\ counter'  = counter
    /\ seenFour'= seenFour \/ (big' = 4)

Next ==
  \/ FillSmall
  \/ EmptySmall
  \/ PourSmallToBig
  \/ FillBig
  \/ EmptyBig
  \/ PourBigToSmall

Stutter ==
  /\ small'   = small
  /\ big'     = big
  /\ counter' = counter
  /\ seenFour'= seenFour

NextState == Next \/ Stutter

Spec == Init /\ [][NextState]_<<small, big, counter, seenFour>>

SafetyInvariant == \always (seenFour)

LivenessBig4 == \diamond (big = 4)

FullSpec == Spec /\ SafetyInvariant /\ LivenessBig4
```