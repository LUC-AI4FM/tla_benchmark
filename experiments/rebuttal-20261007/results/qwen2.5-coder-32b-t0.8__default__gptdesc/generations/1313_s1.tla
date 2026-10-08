```tla
---- MODULE DieHard ----
EXTENDS Naturals, TLC

CONSTANTS smallCap, bigCap
VARIABLES smallJug, bigJug, waterUsage

Init == /\ smallJug = 0 
        /\ bigJug = 0 
        /\ waterUsage = 0

FillSmall == /\ smallJug' = smallCap
               /\ bigJug' = bigJug
               /\ waterUsage' = waterUsage + (smallCap - smallJug)

FillBig == /\ smallJug' = smallJug
             /\ bigJug' = bigCap
             /\ waterUsage' = waterUsage + (bigCap - bigJug)

EmptySmall == /\ smallJug' = 0
                /\ bigJug' = bigJug
                /\ waterUsage' = waterUsage

EmptyBig == /\ smallJug' = smallJug
              /\ bigJug' = 0
              /\ waterUsage' = waterUsage

PourSmallToBig == LET transferAmount == MIN(smallJug, bigCap - bigJug) IN
                    /\ smallJug' = smallJug - transferAmount
                    /\ bigJug' = bigJug + transferAmount
                    /\ waterUsage' = waterUsage

PourBigToSmall == LET transferAmount == MIN(bigJug, smallCap - smallJug) IN
                    /\ smallJug' = smallJug + transferAmount
                    /\ bigJug' = bigJug - transferAmount
                    /\ waterUsage' = waterUsage

Next == FillSmall \/ FillBig \/ EmptySmall \/ EmptyBig \/ PourSmallToBig \/ PourBigToSmall

Spec == Init /\ [][Next]_<<smallJug, bigJug, waterUsage>>

Invariant1 == bigJug \in 0..bigCap
Invariant2 == smallJug \in 0..smallCap

SpecWithInvariants == Spec /\ [](Invariant1 /\ Invariant2)

GoalState == \E s \in States: s.bigJug = 4

ActionCountBound == \A a \in {"FillSmall", "FillBig", "EmptySmall", "EmptyBig", "PourSmallToBig", "PourBigToSmall"}: 
                      Len(Actions(a)) <= 20

StateCountBound == Len(States) <= 50

FairnessSpec == WF_next(<<smallJug, bigJug, waterUsage>>)

CompleteSpec == SpecWithInvariants /\ GoalState /\ ActionCountBound /\ StateCountBound /\ FairnessSpec
```