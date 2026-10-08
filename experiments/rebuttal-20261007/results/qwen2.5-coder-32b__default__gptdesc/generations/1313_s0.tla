------------------------------- MODULE DieHard -------------------------------
EXTENDS Naturals, TLC

CONSTANTS smallCapacity, bigCapacity
VARIABLES smallJug, bigJug, waterUsageCounter

Init == /\ smallJug = 0 
        /\ bigJug = 0 
        /\ waterUsageCounter = 0

FillSmall == /\ smallJug < smallCapacity 
             /\ smallJug' = smallCapacity 
             /\ bigJug' = bigJug 
             /\ waterUsageCounter' = waterUsageCounter + (smallCapacity - smallJug)

FillBig == /\ bigJug < bigCapacity 
           /\ bigJug' = bigCapacity 
           /\ smallJug' = smallJug 
           /\ waterUsageCounter' = waterUsageCounter + (bigCapacity - bigJug)

EmptySmall == /\ smallJug > 0 
              /\ smallJug' = 0 
              /\ bigJug' = bigJug 
              /\ waterUsageCounter' = waterUsageCounter

EmptyBig == /\ bigJug > 0 
            /\ bigJug' = 0 
            /\ smallJug' = smallJug 
            /\ waterUsageCounter' = waterUsageCounter

PourSmallToBig == /\ smallJug > 0 
                  /\ bigJug < bigCapacity 
                  /\ LET transferAmount == MIN(smallJug, bigCapacity - bigJug) IN
                     smallJug' = smallJug - transferAmount 
                     /\ bigJug' = bigJug + transferAmount 
                     /\ waterUsageCounter' = waterUsageCounter

PourBigToSmall == /\ bigJug > 0 
                  /\ smallJug < smallCapacity 
                  /\ LET transferAmount == MIN(bigJug, smallCapacity - smallJug) IN
                     bigJug' = bigJug - transferAmount 
                     /\ smallJug' = smallJug + transferAmount 
                     /\ waterUsageCounter' = waterUsageCounter

Next == \/ FillSmall 
        \/ FillBig 
        \/ EmptySmall 
        \/ EmptyBig 
        \/ PourSmallToBig 
        \/ PourBigToSmall

Spec == Init /\ [][Next]_<<smallJug, bigJug, waterUsageCounter>>

Invariant1 == bigJug \in 0..bigCapacity
Invariant2 == smallJug \in 0..smallCapacity
Invariant3 == waterUsageCounter >= 0

DesiredState == \/ bigJug = 4

SpecWithInvariants == Spec /\ WF_next(Next) /\ Invariant1 /\ Invariant2 /\ Invariant3

(* Fairness conditions *)
FairFillSmall == WF_next(FillSmall)
FairFillBig == WF_next(FillBig)
FairEmptySmall == WF_next(EmptySmall)
FairEmptyBig == WF_next(EmptyBig)
FairPourSmallToBig == WF_next(PourSmallToBig)
FairPourBigToSmall == WF_next(PourBigToSmall)

SpecWithFairness == SpecWithInvariants /\ FairFillSmall /\ FairFillBig /\ FairEmptySmall /\ FairEmptyBig /\ FairPourSmallToBig /\ FairPourBigToSmall

(* TLC-specific operators *)
CONSTANTS _tc
AssumeDesiredState == <>(bigJug = 4)
ActionCountExpectation == \/ (Cardinality({s \in _tc : s.bigJug' - s.bigJug > 0}) >= 1) 
                         \/ (Cardinality({s \in _tc : s.smallJug' - s.smallJug > 0}) >= 1)

SpecForTLC == SpecWithFairness /\ AssumeDesiredState /\ ActionCountExpectation
=============================================================================