------------------------------- MODULE DieHard -------------------------------
EXTENDS Integers, TLC

CONSTANTS BigJugCapacity, SmallJugCapacity

VARIABLES BigJug, SmallJug, WaterUsageCounter

Init == /\ BigJug = 0
        /\ SmallJug = 0
        /\ WaterUsageCounter = 0

FillBigJug ==
    \/ /\ BigJug < BigJugCapacity
       /\ BigJug' = BigJugCapacity
       /\ SmallJug' = SmallJug
       /\ WaterUsageCounter' = WaterUsageCounter + (BigJugCapacity - BigJug)
    \/ UNCHANGED <<BigJug, SmallJug, WaterUsageCounter>>

EmptyBigJug ==
    \/ /\ BigJug > 0
       /\ BigJug' = 0
       /\ SmallJug' = SmallJug
       /\ WaterUsageCounter' = WaterUsageCounter + BigJug
    \/ UNCHANGED <<BigJug, SmallJug, WaterUsageCounter>>

FillSmallJug ==
    \/ /\ SmallJug < SmallJugCapacity
       /\ SmallJug' = SmallJugCapacity
       /\ BigJug' = BigJug
       /\ WaterUsageCounter' = WaterUsageCounter + (SmallJugCapacity - SmallJug)
    \/ UNCHANGED <<BigJug, SmallJug, WaterUsageCounter>>

EmptySmallJug ==
    \/ /\ SmallJug > 0
       /\ SmallJug' = 0
       /\ BigJug' = BigJug
       /\ WaterUsageCounter' = WaterUsageCounter + SmallJug
    \/ UNCHANGED <<BigJug, SmallJug, WaterUsageCounter>>

PourFromSmallToBig ==
    \/ /\ SmallJug > 0
       /\ BigJug < BigJugCapacity
       /\ Let amountToPour \in {MIN(SmallJug, BigJugCapacity - BigJug)} 
          IN SmallJug' = SmallJug - amountToPour 
             /\ BigJug' = BigJug + amountToPour
             /\ WaterUsageCounter' = WaterUsageCounter
    \/ UNCHANGED <<BigJug, SmallJug, WaterUsageCounter>>

PourFromBigToSmall ==
    \/ /\ BigJug > 0
       /\ SmallJug < SmallJugCapacity
       /\ Let amountToPour \in {MIN(BigJug, SmallJugCapacity - SmallJug)} 
          IN BigJug' = BigJug - amountToPour 
             /\ SmallJug' = SmallJug + amountToPour
             /\ WaterUsageCounter' = WaterUsageCounter
    \/ UNCHANGED <<BigJug, SmallJug, WaterUsageCounter>>

Next ==
    \/ FillBigJug
    \/ EmptyBigJug
    \/ FillSmallJug
    \/ EmptySmallJug
    \/ PourFromSmallToBig
    \/ PourFromBigToSmall

Spec == Init /\ [][Next]_<<BigJug, SmallJug, WaterUsageCounter>>

StateConstraint ==
    /\ BigJug \in 0..BigJugCapacity
    /\ SmallJug \in 0..SmallJugCapacity
    /\ WaterUsageCounter >= 0

Invariant ==
    StateConstraint

SafetyProperty ==
    Spec /\ [](StateConstraint)

LivenessProperty ==
    Spec /\ <>(BigJug = 4)

ActionStateCountExpectations ==
    TLCGet("states") > 15
    /\ TLCGet("actions") >= 6

====