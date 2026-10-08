MODULE DieHardWaterJug
EXTENDS Naturals, Integers, TLC

CONSTANTS SMALL_CAP, BIG_CAP

VARIABLES small, big, usage

Init == /\ small = 0
        /\ big = 0
        /\ usage = 0

FillSmall ==
    /\ small' = SMALL_CAP
    /\ big'   = big
    /\ usage' = usage + 1

EmptySmall ==
    /\ small' = 0
    /\ big'   = big
    /\ usage' = usage

FillBig ==
    /\ big'   = BIG_CAP
    /\ small' = small
    /\ usage' = usage + 1

EmptyBig ==
    /\ big'   = 0
    /\ small' = small
    /\ usage' = usage

PourSmallToBig == 
    LET transfer == Min(small, BIG_CAP - big) IN
    /\ small' = small - transfer
    /\ big'   = big + transfer
    /\ usage' = usage

PourBigToSmall ==
    LET transfer == Min(big, SMALL_CAP - small) IN
    /\ big'   = big - transfer
    /\ small' = small + transfer
    /\ usage' = usage

Stutter ==
    /\ small' = small
    /\ big'   = big
    /\ usage' = usage

Next == \/ FillSmall
        \/ EmptySmall
        \/ FillBig
        \/ EmptyBig
        \/ PourSmallToBig
        \/ PourBigToSmall
        \/ Stutter

SafetyInvariant == /\ small <= SMALL_CAP
                   /\ big   <= BIG_CAP
                   /\ usage >= 0

Spec == Init /\ [][Next]_<<small,big,usage>> /\ SafetyInvariant

THEOREM BigFourReachable == <> (big = 4)