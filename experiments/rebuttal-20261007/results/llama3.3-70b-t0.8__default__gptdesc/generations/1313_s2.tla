```
MODULE DieHardWaterJug
EXTENDS Integers, TLC
CONSTANTS CapacitySmall, CapacityBig
VARIABLES smallJug, bigJug, waterUsage, steps

Init ==
  /\ smallJug = 0
  /\ bigJug = 0
  /\ waterUsage = 0
  /\ steps = 0

Next ==
  \/ FillSmall == 
    /\ smallJug' = CapacitySmall
    /\ bigJug' = bigJug
    /\ waterUsage' = waterUsage + CapacitySmall - smallJug
    /\ steps' = steps + 1
  \/ FillBig == 
    /\ smallJug' = smallJug
    /\ bigJug' = CapacityBig
    /\ waterUsage' = waterUsage + CapacityBig - bigJug
    /\ steps' = steps + 1
  \/ EmptySmall == 
    /\ smallJug' = 0
    /\ bigJug' = bigJug
    /\ waterUsage' = waterUsage
    /\ steps' = steps + 1
  \/ EmptyBig == 
    /\ smallJug' = smallJug
    /\ bigJug' = 0
    /\ waterUsage' = waterUsage
    /\ steps' = steps + 1
  \/ PourSmallToBig == 
    /\ smallJug >= CapacityBig - bigJug
    /\ smallJug' = smallJug - (CapacityBig - bigJug)
    /\ bigJug' = CapacityBig
    /\ waterUsage' = waterUsage
    /\ steps' = steps + 1
  \/ PourBigToSmall == 
    /\ bigJug >= CapacitySmall - smallJug
    /\ smallJug' = CapacitySmall
    /\ bigJug' = bigJug - (CapacitySmall - smallJug)
    /\ waterUsage' = waterUsage
    /\ steps' = steps + 1
  \/ PourSmallToBigPartial == 
    /\ smallJug < CapacityBig - bigJug
    /\ smallJug' = 0
    /\ bigJug' = bigJug + smallJug
    /\ waterUsage' = waterUsage
    /\ steps' = steps + 1
  \/ PourBigToSmallPartial == 
    /\ bigJug < CapacitySmall - smallJug
    /\ smallJug' = smallJug + bigJug
    /\ bigJug' = 0
    /\ waterUsage' = waterUsage
    /\ steps' = steps + 1

Spec ==
  Init /\ [][Next]_<<smallJug, bigJug, waterUsage, steps>>

THEOREM Spec => []<>(bigJug = 4)
THEOREM Spec => <>((steps > 10) => (waterUsage > 20))

Fairness == SF_Vars(steps)

```
Note: The values of `CapacitySmall` and `CapacityBig` should be set to 3 and 5 respectively in the model file for TLC.