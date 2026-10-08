---- MODULE DieHard ----
EXTENDS Naturals, TLC

CONSTANTS smallCap, bigCap
VARIABLES smallJug, bigJug, waterUsedCounter

Init == /\ smallJug = 0 
        /\ bigJug = 0 
        /\ waterUsedCounter = 0

FillSmall == smallJug' = smallCap \* bigJug' = bigJug \* waterUsedCounter' = waterUsedCounter + (smallCap - smallJug)

FillBig == /\ bigJug' = bigCap 
           /\ smallJug' = smallJug 
           /\ waterUsedCounter' = waterUsedCounter + (bigCap - bigJug)

EmptySmall == /\ smallJug' = 0 
              /\ bigJug' = bigJug 
              /\ waterUsedCounter' = waterUsedCounter

EmptyBig == /\ bigJug' = 0 
            /\ smallJug' = smallJug 
            /\ waterUsedCounter' = waterUsedCounter

PourSmallToBig == /\ bigJug' <= bigCap
                   /\ bigJug' = Min(bigJug + smallJug, bigCap)
                   /\ smallJug' = Max(smallJug - (bigCap - bigJug), 0)
                   /\ waterUsedCounter' = waterUsedCounter

PourBigToSmall == /\ smallJug' <= smallCap
                   /\ smallJug' = Min(smallJug + bigJug, smallCap)
                   /\ bigJug' = Max(bigJug - (smallCap - smallJug), 0)
                   /\ waterUsedCounter' = waterUsedCounter

Next == \/ FillSmall 
        \/ FillBig 
        \/ EmptySmall 
        \/ EmptyBig 
        \/ PourSmallToBig 
        \/ PourBigToSmall

Spec == Init /\ [][Next]_<<smallJug, bigJug, waterUsedCounter>>

INVARIANT Spec => bigJug \in 0..bigCap
INVARIANT Spec => smallJug \in 0..smallCap
INVARIANT Spec => waterUsedCounter >= 0

TEMPORAL_PROPERTY_1 == <>(bigJug = 4)
TEMPORAL_PROPERTY_2 == [](waterUsedCounter <= bigCap + smallCap)

====