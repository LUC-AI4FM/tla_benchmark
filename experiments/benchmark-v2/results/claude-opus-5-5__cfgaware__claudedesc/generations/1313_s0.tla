---------------------------- MODULE DieHardTLA ----------------------------
EXTENDS Naturals, TLC

VARIABLES small, big

vars == <<small, big>>

TypeOK == /\ small \in 0..3
          /\ big   \in 0..5

Min(m, n) == IF m < n THEN m ELSE n

Init == /\ small = 0
        /\ big = 0
        /\ TLCSet(42, 0)
        /\ TLCSet(43, 0)
        /\ TLCSet(44, 0)

FillSmall == /\ TLCSet(42, TLCGet(42) + (3 - small))
             /\ small' = 3
             /\ big' = big

FillBig == /\ TLCSet(42, TLCGet(42) + (5 - big))
           /\ big' = 5
           /\ small' = small

EmptySmall == /\ small' = 0
              /\ big' = big

EmptyBig == /\ big' = 0
            /\ small' = small

SmallToBig == /\ big'   = Min(big + small, 5)
              /\ small' = small - (big' - big)

BigToSmall == /\ small' = Min(big + small, 3)
              /\ big'   = big - (small' - small)

Next == \/ FillSmall
        \/ FillBig
        \/ EmptySmall
        \/ EmptyBig
        \/ SmallToBig
        \/ BigToSmall

Spec == Init /\ [][Next]_vars

HasFour == big = 4

PourAction == /\ small' # small
              /\ big' # big

_POSSIBLE == /\ (HasFour => TLCSet(43, TLCGet(43) + 1))
             /\ (PourAction => TLCSet(44, TLCGet(44) + 1))

PossibleCounts == /\ TLCGet(43) = 8
                  /\ TLCGet(44) = 14

PostCondition == /\ TLCGet("stats").generated = 97
                 /\ TLCGet("stats").distinct = 16
                 /\ TLCGet("stats").diameter = 8
                 /\ TLCGet(42) = 128
=============================================================================