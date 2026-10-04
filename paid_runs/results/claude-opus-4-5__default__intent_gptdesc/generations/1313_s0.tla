---------------------------- MODULE WaterJugs ----------------------------

EXTENDS Integers, Naturals

CONSTANTS SmallCap, BigCap

ASSUME SmallCap = 3
ASSUME BigCap = 5

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

PourSmallToBig ==
    LET amount == IF small + big <= BigCap
                  THEN small
                  ELSE BigCap - big
    IN /\ small' = small - amount
       /\ big' = big + amount
       /\ waterDrawn' = waterDrawn

PourBigToSmall ==
    LET amount == IF small + big <= SmallCap
                  THEN big
                  ELSE SmallCap - small
    IN /\ small' = small - amount
       /\ big' = big + amount
       /\ waterDrawn' = waterDrawn

Change ==
    \/ FillSmall
    \/ FillBig
    \/ EmptySmall
    \/ EmptyBig
    \/ PourSmallToBig
    \/ PourBigToSmall

Next == Change

Spec == Init /\ [][Next]_vars

BigHasFour == big = 4

GoalReached == big = 4

ContentChanged == (small' # small) \/ (big' # big)

ChangeAction == Next /\ ContentChanged

SafetyInvariant == TypeOK

GoalState == big = 4

\* ============================================================================