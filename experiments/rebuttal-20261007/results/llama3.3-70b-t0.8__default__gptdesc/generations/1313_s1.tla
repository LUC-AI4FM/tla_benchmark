```
MODULE DieHard
EXTENDS Integers, TLC
CONSTANTS CapacitySmall, CapacityBig
VARIABLES smallJug, bigJug, waterUsage

Init ==
  /\ smallJug = 0
  /\ bigJug = 0
  /\ waterUsage = 0

Next ==
  \/ FillSmall ==>
    /\ smallJug' = CapacitySmall
    /\ bigJug' = bigJug
    /\ waterUsage' = waterUsage + 1
  \/ FillBig ==>
    /\ smallJug' = smallJug
    /\ bigJug' = CapacityBig
    /\ waterUsage' = waterUsage + 1
  \/ EmptySmall ==>
    /\ smallJug' = 0
    /\ bigJug' = bigJug
    /\ waterUsage' = waterUsage
  \/ EmptyBig ==>
    /\ smallJug' = smallJug
    /\ bigJug' = 0
    /\ waterUsage' = waterUsage
  \/ PourSmallToBig ==>
    /\ smallJug >= CapacityBig - bigJug
    /\ smallJug' = smallJug - (CapacityBig - bigJug)
    /\ bigJug' = CapacityBig
    /\ waterUsage' = waterUsage
  \/ PourBigToSmall ==>
    /\ bigJug >= CapacitySmall - smallJug
    /\ smallJug' = CapacitySmall
    /\ bigJug' = bigJug - (CapacitySmall - smallJug)
    /\ waterUsage' = waterUsage
  \/ UNCHANGED <<smallJug, bigJug, waterUsage>>

Spec == Init /\ [][Next]_<<smallJug, bigJug, waterUsage>>
  
THEOREM Spec => []<>(bigJug = 4)

THEOREM Spec => <>[](waterUsage > 10)
```
Note: This specification uses the TLC-specific operators to track and inspect model-checking statistics. The custom counter of water usage is also defined as a variable `waterUsage`. The predicates intended to check that the state space contains a state where the big jug has 4 gallons and that certain action/state-count expectations hold after model checking are defined using THEOREM statements.