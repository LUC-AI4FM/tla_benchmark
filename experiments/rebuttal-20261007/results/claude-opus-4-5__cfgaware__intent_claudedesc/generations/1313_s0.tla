---------------------------- MODULE DieHard ----------------------------
EXTENDS Integers, TLC

CONSTANTS SmallCap, BigCap

VARIABLES small, big, totalDrawn

vars == <<small, big, totalDrawn>>

TypeOK == /\ small \in 0..SmallCap
          /\ big \in 0..BigCap
          /\ totalDrawn \in Nat

Init == /\ small = 0
        /\ big = 0
        /\ totalDrawn = 0

FillSmall == /\ small' = SmallCap
             /\ big' = big
             /\ totalDrawn' = totalDrawn + (SmallCap - small)

FillBig == /\ big' = BigCap
           /\ small' = small
           /\ totalDrawn' = totalDrawn + (BigCap - big)

EmptySmall == /\ small' = 0
              /\ big' = big
              /\ totalDrawn' = totalDrawn

EmptyBig == /\ big' = 0
            /\ small' = small
            /\ totalDrawn' = totalDrawn

SmallToBig == LET pour == IF small + big <= BigCap
                          THEN small
                          ELSE BigCap - big
              IN /\ small' = small - pour
                 /\ big' = big + pour
                 /\ totalDrawn' = totalDrawn

BigToSmall == LET pour == IF small + big <= SmallCap
                          THEN big
                          ELSE SmallCap - small
              IN /\ small' = small + pour
                 /\ big' = big - pour
                 /\ totalDrawn' = totalDrawn

Next == \/ FillSmall
        \/ FillBig
        \/ EmptySmall
        \/ EmptyBig
        \/ SmallToBig
        \/ BigToSmall

Spec == Init /\ [][Next]_vars

BigHasFour == big = 4

NotBigHasFour == big # 4

BothJugsChange == /\ small' # small
                  /\ big' # big

CountBothJugsChange == 
    LET SmallToBigChanges == IF small > 0 /\ big < BigCap THEN 1 ELSE 0
        BigToSmallChanges == IF big > 0 /\ small < SmallCap THEN 1 ELSE 0
    IN SmallToBigChanges + BigToSmallChanges

=============================================================================