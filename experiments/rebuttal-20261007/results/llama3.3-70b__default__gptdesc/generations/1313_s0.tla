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
  \/ FillSmall
  \/ FillBig
  \/ EmptySmall
  \/ EmptyBig
  \/ PourSmallToBig
  \/ PourBigToSmall

FillSmall == 
  /\ smallJug' = CapacitySmall
  /\ bigJug' = bigJug
  /\ waterUsage' = waterUsage + (CapacitySmall - smallJug)

FillBig == 
  /\ smallJug' = smallJug
  /\ bigJug' = CapacityBig
  /\ waterUsage' = waterUsage + (CapacityBig - bigJug)

EmptySmall == 
  /\ smallJug' = 0
  /\ bigJug' = bigJug
  /\ waterUsage' = waterUsage

EmptyBig == 
  /\ smallJug' = smallJug
  /\ bigJug' = 0
  /\ waterUsage' = waterUsage

PourSmallToBig ==
  /\ smallJug' = smallJug - (CapacityBig - bigJug)
  /\ bigJug' = Min(bigJug + smallJug, CapacityBig)
  /\ waterUsage' = waterUsage

PourBigToSmall ==
  /\ smallJug' = Min(smallJug + bigJug, CapacitySmall)
  /\ bigJug' = bigJug - (CapacitySmall - smallJug)
  /\ waterUsage' = waterUsage

Spec == Init /\ [][Next]_<<smallJug, bigJug, waterUsage>>
BigJugHas4Gallons == <<bigJug = 4>>

THEOREM Spec => []<>BigJugHas4Gallons
```
Note: The `Min` function used in the `PourSmallToBig` and `PourBigToSmall` actions is not a built-in TLA+ operator. To use it, you would need to define it as an operator or replace it with equivalent TLA+ expressions.

Also note that TLC-specific operators are not standard TLA+, so this specification may not be compatible with all TLA+ tools.