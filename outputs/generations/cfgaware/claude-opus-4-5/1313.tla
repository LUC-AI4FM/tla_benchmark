---------------------------- MODULE die_hard ----------------------------
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
    LET amount == IF small + big <= BigCapacity THEN small ELSE BigCapacity - big
    IN /\ big' = big + amount
       /\ small' = small - amount
       /\ waterUsed' = waterUsed

BigToSmall ==
    LET amount == IF small + big <= SmallCapacity THEN big ELSE SmallCapacity - small
    IN /\ small' = small + amount
       /\ big' = big - amount
       /\ waterUsed' = waterUsed

Next ==
    \/ FillSmall
    \/ FillBig
    \/ EmptySmall
    \/ EmptyBig
    \/ SmallToBig
    \/ BigToSmall

Spec == Init /\ [][Next]_vars

BigHas4 == big = 4

NotBigHas4 == big # 4

StateCount == TLCGet("distinct")

ActionCount == TLCGet("generated")

CheckStateCount(expected) == StateCount >= expected

CheckActionCount(expected) == ActionCount >= expected

StatsInvariant == 
    /\ TLCGet("distinct") >= 0
    /\ TLCGet("generated") >= 0

WaterUsageInvariant == waterUsed >= 0

==========================================================================