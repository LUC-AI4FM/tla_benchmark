```
MODULE DieHardWaterJug
EXTENDS Integers, TLC
CONSTANTS CapacitySmall, CapacityBig
VARIABLES smallJug, bigJug, waterUsage

Init ==
  /\ smallJug = 0
  /\ bigJug = 0
  /\ waterUsage = 0

Next ==
  \/ FillSmall == 
    /\ smallJug' = CapacitySmall
    /\ bigJug' = bigJug
    /\ waterUsage' = waterUsage + (CapacitySmall - smallJug)
  \/ FillBig == 
    /\ smallJug' = smallJug
    /\ bigJug' = CapacityBig
    /\ waterUsage' = waterUsage + (CapacityBig - bigJug)
  \/ EmptySmall == 
    /\ smallJug' = 0
    /\ bigJug' = bigJug
    /\ waterUsage' = waterUsage
  \/ EmptyBig == 
    /\ smallJug' = smallJug
    /\ bigJug' = 0
    /\ waterUsage' = waterUsage
  \/ PourSmallToBig == 
    /\ smallJug' = 0
    /\ bigJug' = bigJug + smallJug
    /\ waterUsage' = waterUsage
    /\ bigJug + smallJug <= CapacityBig
  \/ PourBigToSmall == 
    /\ smallJug' = smallJug + bigJug
    /\ bigJug' = 0
    /\ waterUsage' = waterUsage
    /\ smallJug + bigJug <= CapacitySmall

Spec ==
  Init /\ [][Next]_<<smallJug, bigJug, waterUsage>>
  
Fairness == 
  <>[]<>(bigJug = 4)

THEOREM Spec => []<>Fairness
INVARIANT smallJug >= 0 /\ smallJug <= CapacitySmall
INVARIANT bigJug >= 0 /\ bigJug <= CapacityBig

```
Note: To use TLC-specific operators to track and inspect model-checking statistics, you would need to write additional code in a separate file or module that uses the TLC API. This TLA+ specification does not include such code as it only describes the system's behavior using TLA+.