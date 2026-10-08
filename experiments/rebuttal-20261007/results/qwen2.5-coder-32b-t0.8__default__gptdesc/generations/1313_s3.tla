------------------------------- MODULE DieHard -------------------------------
EXTENDS Naturals, TLC

CONSTANTS SmallCapacity, BigCapacity

VARIABLES smallJug, bigJug, waterUsageCounter

Init == /\ smallJug = 0
        /\ bigJug = 0
        /\ waterUsageCounter = 0

FillSmall ==
    /\ smallJug < SmallCapacity
    /\ smallJug' = SmallCapacity
    /\ bigJug' = bigJug
    /\ waterUsageCounter' = waterUsageCounter + (SmallCapacity - smallJug)

FillBig ==
    /\ bigJug < BigCapacity
    /\ bigJug' = BigCapacity
    /\ smallJug' = smallJug
    /\ waterUsageCounter' = waterUsageCounter + (BigCapacity - bigJug)

EmptySmall ==
    /\ smallJug > 0
    /\ smallJug' = 0
    /\ bigJug' = bigJug
    /\ waterUsageCounter' = waterUsageCounter

EmptyBig ==
    /\ bigJug > 0
    /\ bigJug' = 0
    /\ smallJug' = smallJug
    /\ waterUsageCounter' = waterUsageCounter

PourSmallToBig ==
    /\ smallJug > 0
    /\ bigJug < BigCapacity
    /\ LET amountToPour == MIN(smallJug, BigCapacity - bigJug)
       IN /\ smallJug' = smallJug - amountToPour
          /\ bigJug' = bigJug + amountToPour
          /\ waterUsageCounter' = waterUsageCounter

PourBigToSmall ==
    /\ bigJug > 0
    /\ smallJug < SmallCapacity
    /\ LET amountToPour == MIN(bigJug, SmallCapacity - smallJug)
       IN /\ bigJug' = bigJug - amountToPour
          /\ smallJug' = smallJug + amountToPour
          /\ waterUsageCounter' = waterUsageCounter

Next ==
    \/ FillSmall
    \/ FillBig
    \/ EmptySmall
    \/ EmptyBig
    \/ PourSmallToBig
    \/ PourBigToSmall

Spec == Init /\ [][Next]_<<smallJug, bigJug, waterUsageCounter>>

Inv == /\ smallJug \in 0..SmallCapacity
       /\ bigJug \in 0..BigCapacity
       /\ waterUsageCounter >= 0

Reach4Gallons ==
    <>(bigJug = 4)

ActionCountExpectations ==
    /\ TLCGet("States") > 10
    /\ TLCGet("Actions") > 5

Fairness == WF_vars(<<FillSmall, FillBig, EmptySmall, EmptyBig, PourSmallToBig, PourBigToSmall>>, <<smallJug, bigJug, waterUsageCounter>>)

THEOREM Spec => []Inv
THEOREM Spec => <>Reach4Gallons
THEOREM Spec => ActionCountExpectations

=============================================================================