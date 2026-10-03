---------------------------- MODULE DieHard ----------------------------
EXTENDS Integers, TLC

CONSTANTS SmallCapacity, BigCapacity

VARIABLES small, big, waterUsed

vars == <<small, big, waterUsed>>

TypeOK == 
    /\ small \in 0..SmallCapacity
    /\ big \in 0..BigCapacity
    /\ waterUsed \in Nat

Init == 
    /\ small = 0
    /\ big = 0
    /\ waterUsed = 0

FillSmall ==
    /\ small' = SmallCapacity
    /\ big' = big
    /\ waterUsed' = waterUsed + (SmallCapacity - small)

FillBig ==
    /\ big' = BigCapacity
    /\ small' = small
    /\ waterUsed' = waterUsed + (BigCapacity - big)

EmptySmall ==
    /\ small' = 0
    /\ big' = big
    /\ waterUsed' = waterUsed

EmptyBig ==
    /\ big' = 0
    /\ small' = small
    /\ waterUsed' = waterUsed

SmallToBig ==
    LET transfer == IF small + big <= BigCapacity
                    THEN small
                    ELSE BigCapacity - big
    IN
    /\ small' = small - transfer
    /\ big' = big + transfer
    /\ waterUsed' = waterUsed

BigToSmall ==
    LET transfer == IF big + small <= SmallCapacity
                    THEN big
                    ELSE SmallCapacity - small
    IN
    /\ big' = big - transfer
    /\ small' = small + transfer
    /\ waterUsed' = waterUsed

Next ==
    \/ FillSmall
    \/ FillBig
    \/ EmptySmall
    \/ EmptyBig
    \/ SmallToBig
    \/ BigToSmall

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

BigHas4 == big = 4

NotBigHas4 == big /= 4

GoalReachable == 
    LET stats == TLCGet("stats")
    IN \E s \in DOMAIN stats : TRUE

CheckDistinctStates == 
    TLCGet("distinct") > 0

CheckGeneratedStates ==
    TLCGet("generated") > 0

StateSpaceExplored ==
    /\ CheckDistinctStates
    /\ CheckGeneratedStates

GoalStateExists == 
    ~NotBigHas4

WaterUsageInvariant == waterUsed >= 0

SafetyInvariant ==
    /\ TypeOK
    /\ WaterUsageInvariant
    /\ small >= 0
    /\ big >= 0
    /\ small <= SmallCapacity
    /\ big <= BigCapacity

-----------------------------------------------------------------------------

Liveness == <>(big = 4)

FairSpec == Spec /\ WF_vars(Next)

==========================================================================