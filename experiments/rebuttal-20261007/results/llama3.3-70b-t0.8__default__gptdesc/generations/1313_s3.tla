```
MODULE DieHard
EXTENDS Integers
CONSTANTS CapacitySmall, CapacityBig
VARIABLES smallJug, bigJug, waterUsage, steps

Init ==
  /\ smallJug = 0
  /\ bigJug = 0
  /\ waterUsage = 0
  /\ steps = 0

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
  /\ steps' = steps + 1

FillBig == 
  /\ bigJug' = CapacityBig
  /\ smallJug' = smallJug
  /\ waterUsage' = waterUsage + (CapacityBig - bigJug)
  /\ steps' = steps + 1

EmptySmall == 
  /\ smallJug' = 0
  /\ bigJug' = bigJug
  /\ waterUsage' = waterUsage
  /\ steps' = steps + 1

EmptyBig == 
  /\ bigJug' = 0
  /\ smallJug' = smallJug
  /\ waterUsage' = waterUsage
  /\ steps' = steps + 1

PourSmallToBig ==
  /\ smallJug >= 0
  /\ bigJug <= CapacityBig
  /\ smallJug' = smallJug - (CapacityBig - bigJug)
  /\ bigJug' = min(bigJug + smallJug, CapacityBig)
  /\ waterUsage' = waterUsage
  /\ steps' = steps + 1

PourBigToSmall ==
  /\ smallJug <= CapacitySmall
  /\ bigJug >= 0
  /\ smallJug' = min(capacitySmall, smallJug + bigJug)
  /\ bigJug' = bigJug - (CapacitySmall - smallJug)
  /\ waterUsage' = waterUsage
  /\ steps' = steps + 1

Spec == Init /\ [][Next]_<<smallJug, bigJug, waterUsage, steps>>
Fairness == <>[](bigJug = 4)

THEOREM Spec => []Fairness
```
Note: The SANY parser may report an error if the CapacitySmall and CapacityBig constants are not replaced with their actual values (3 and 5 respectively) in the above specification. Replace these constants to obtain a valid TLA+ module that can be parsed by SANY.

Also, TLC-specific operators for tracking model-checking statistics have been omitted from this specification as they may vary based on specific usage. The `waterUsage` variable serves as a custom counter of water usage as described in the problem statement.