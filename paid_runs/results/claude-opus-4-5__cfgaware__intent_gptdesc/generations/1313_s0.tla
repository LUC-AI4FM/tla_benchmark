---------------------------- MODULE waterjugs ----------------------------

EXTENDS Integers, Naturals, TLC

CONSTANTS SmallCap, BigCap

VARIABLES small, big, waterDrawn

vars == <<small, big, waterDrawn>>

TypeOK ==
    /\ small \in 0..SmallCap
    /\ big \in 0..BigCap
    /\ waterDrawn \in Nat

Init ==
    /\ small = 0
    /\ big = 0
    /\ waterDrawn = 0

FillSmall ==
    /\ small' = SmallCap
    /\ big' = big
    /\ waterDrawn' = waterDrawn + (SmallCap - small)

FillBig ==
    /\ big' = BigCap
    /\ small' = small
    /\ waterDrawn' = waterDrawn + (BigCap - big)

EmptySmall ==
    /\ small' = 0
    /\ big' = big
    /\ waterDrawn' = waterDrawn

EmptyBig ==
    /\ big' = 0
    /\ small' = small
    /\ waterDrawn' = waterDrawn

SmallToBig ==
    LET amount == IF small + big <= BigCap THEN small ELSE BigCap - big
    IN
        /\ small' = small - amount
        /\ big' = big + amount
        /\ waterDrawn' = waterDrawn

BigToSmall ==
    LET amount == IF small + big <= SmallCap THEN big ELSE SmallCap - small
    IN
        /\ small' = small + amount
        /\ big' = big - amount
        /\ waterDrawn' = waterDrawn

Next ==
    \/ FillSmall
    \/ FillBig
    \/ EmptySmall
    \/ EmptyBig
    \/ SmallToBig
    \/ BigToSmall

Spec == Init /\ [][Next]_vars

BigHasFour == big = 4

NotBigHasFour == big # 4

Change == (small' # small) \/ (big' # big)

PourOrChange == <<Next /\ Change>>_vars

GeneratedStates == 16

DistinctStates == 16

Diameter == 7

TotalWaterDrawn == 56

AvgWaterPerState == 3

=============================================================================