------------------------------ MODULE DieHardWaterJug ------------------------------
EXTENDS Naturals, TLC

CONSTANTS SMALL_CAPACITY, BIG_CAPACITY

SMALL_CAPACITY == 3
BIG_CAPACITY   == 5

VARIABLES small, big, waterUsed

FillSmall ==
   /\ small' = SMALL_CAPACITY
   /\ big'   = big
   /\ waterUsed' = waterUsed + (SMALL_CAPACITY - small)

EmptySmall ==
   /\ small' = 0
   /\ big'   = big
   /\ waterUsed' = waterUsed

FillBig ==
   /\ big'   = BIG_CAPACITY
   /\ small' = small
   /\ waterUsed' = waterUsed + (BIG_CAPACITY - big)

EmptyBig ==
   /\ big'   = 0
   /\ small' = small
   /\ waterUsed' = waterUsed

PourSmallToBig ==
   LET transfer == MIN(small, BIG_CAPACITY - big) IN
   /\ small' = small - transfer
   /\ big'   = big + transfer
   /\ waterUsed' = waterUsed

PourBigToSmall ==
   LET transfer == MIN(big, SMALL_CAPACITY - small) IN
   /\ big'   = big - transfer
   /\ small' = small + transfer
   /\ waterUsed' = waterUsed

Stutter ==
   /\ small'   = small
   /\ big'     = big
   /\ waterUsed'= waterUsed

Next == \/ FillSmall
        \/ EmptySmall
        \/ FillBig
        \/ EmptyBig
        \/ PourSmallToBig
        \/ PourBigToSmall
        \/ Stutter

Init ==
   /\ small    = 0
   /\ big      = 0
   /\ waterUsed= 0

Spec == Init /\ [][Next]_<<small, big, waterUsed>>

(* Predicates for checking the state space *)

BigHasFour == (big = 4)

StateCountExpectation ==
   /\ TLCStateCount     >= 10
   /\ TLCTransitionCount>= 20

===============================================================================