---------------------------- MODULE DieHard ----------------------------

EXTENDS Integers, TLC

CONSTANTS SmallCapacity, BigCapacity

VARIABLES small, big, totalDrawn

vars == <<small, big, totalDrawn>>

TypeOK ==
    /\ small \in 0..SmallCapacity
    /\ big \in 0..BigCapacity
    /\ totalDrawn \in Nat

Init ==
    /\ small = 0
    /\ big = 0
    /\ totalDrawn = 0

FillSmall ==
    /\ small' = SmallCapacity
    /\ big' = big
    /\ totalDrawn' = totalDrawn + (SmallCapacity - small)

FillBig ==
    /\ small' = small
    /\ big' = BigCapacity
    /\ totalDrawn' = totalDrawn + (BigCapacity - big)

EmptySmall ==
    /\ small' = 0
    /\ big' = big
    /\ totalDrawn' = totalDrawn

EmptyBig ==
    /\ small' = small
    /\ big' = 0
    /\ totalDrawn' = totalDrawn

SmallToBig ==
    LET amount == IF small + big <= BigCapacity
                  THEN small
                  ELSE BigCapacity - big
    IN /\ small' = small - amount
       /\ big' = big + amount
       /\ totalDrawn' = totalDrawn

BigToSmall ==
    LET amount == IF small + big <= SmallCapacity
                  THEN big
                  ELSE SmallCapacity - small
    IN /\ small' = small + amount
       /\ big' = big - amount
       /\ totalDrawn' = totalDrawn

Next ==
    \/ FillSmall
    \/ FillBig
    \/ EmptySmall
    \/ EmptyBig
    \/ SmallToBig
    \/ BigToSmall

Spec == Init /\ [][Next]_vars

BigJugHasFour == big = 4

NotFour == big # 4

BothJugsChange ==
    /\ small' # small
    /\ big' # big

CountBothChange ==
    \/ (SmallToBig /\ small' # small /\ big' # big)
    \/ (BigToSmall /\ small' # small /\ big' # big)

=========================================================================