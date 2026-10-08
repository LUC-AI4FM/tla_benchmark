MODULE DieHardJug

EXTENDS Naturals, TLC

VARIABLES small, big, totalDrawn, countBig4, countBothChanged

Init ==
  /\ small = 0
  /\ big   = 0
  /\ totalDrawn    = 0
  /\ countBig4     = 0
  /\ countBothChanged = 0

TypeInvariant ==
  /\ small \in 0..3
  /\ big   \in 0..5

FillSmall ==
  /\ small < 3
  /\ LET added == 3 - small IN
       /\ small' = 3
       /\ big'   = big
       /\ totalDrawn'    = totalDrawn + added
       /\ countBig4'     = IF big' = 4 THEN countBig4 + 1 ELSE countBig4
       /\ countBothChanged' = countBothChanged

FillBig ==
  /\ big < 5
  /\ LET added == 5 - big IN
       /\ small' = small
       /\ big'   = 5
       /\ totalDrawn'    = totalDrawn + added
       /\ countBig4'     = IF big' = 4 THEN countBig4 + 1 ELSE countBig4
       /\ countBothChanged' = countBothChanged

EmptySmall ==
  /\ small > 0
  /\ small' = 0
  /\ big'   = big
  /\ totalDrawn'    = totalDrawn
  /\ countBig4'     = IF big' = 4 THEN countBig4 + 1 ELSE countBig4
  /\ countBothChanged' = countBothChanged

EmptyBig ==
  /\ big > 0
  /\ small' = small
  /\ big'   = 0
  /\ totalDrawn'    = totalDrawn
  /\ countBig4'     = IF big' = 4 THEN countBig4 + 1 ELSE countBig4
  /\ countBothChanged' = countBothChanged

PourSmallToBig ==
  /\ small > 0
  /\ big < 5
  /\ LET transfer == Min(small, 5 - big) IN
       /\ small' = small - transfer
       /\ big'   = big + transfer
       /\ totalDrawn'    = totalDrawn
       /\ countBothChanged' = countBothChanged + 1
       /\ countBig4'     = IF big' = 4 THEN countBig4 + 1 ELSE countBig4

PourBigToSmall ==
  /\ big > 0
  /\ small < 3
  /\ LET transfer == Min(big, 3 - small) IN
       /\ big'   = big - transfer
       /\ small' = small + transfer
       /\ totalDrawn'    = totalDrawn
       /\ countBothChanged' = countBothChanged + 1
       /\ countBig4'     = IF big' = 4 THEN countBig4 + 1 ELSE countBig4

Next ==
  \/ FillSmall
  \/ FillBig
  \/ EmptySmall
  \/ EmptyBig
  \/ PourSmallToBig
  \/ PourBigToSmall

Spec == Init /\ [][Next]_<<small,big,totalDrawn,countBig4,countBothChanged>> /\ TypeInvariant

THEOREM BigCanReachFour == <> (big = 4)