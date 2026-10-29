---------------------------- MODULE DieHard ----------------------------
EXTENDS Naturals, TLC

VARIABLES small, big

vars == <<small, big>>

Min(m, n) == IF m < n THEN m ELSE n

(* Register 1 counts water used; register 2 records whether a state with 4 gallons in the big jug was seen. *)
ASSUME TLCSet(1, 0)
ASSUME TLCSet(2, FALSE)

TypeOK == /\ small \in 0..3
          /\ big   \in 0..5

Init == /\ big = 0
        /\ small = 0

FillSmallJug  == /\ small' = 3
                 /\ big' = big
                 /\ TLCSet(1, TLCGet(1) + (3 - small))

FillBigJug    == /\ big' = 5
                 /\ small' = small
                 /\ TLCSet(1, TLCGet(1) + (5 - big))

EmptySmallJug == /\ small' = 0
                 /\ big' = big

EmptyBigJug   == /\ big' = 0
                 /\ small' = small

SmallToBig == /\ big'   = Min(big + small, 5)
              /\ small' = small - (big' - big)

BigToSmall == /\ small' = Min(big + small, 3)
              /\ big'   = big - (small' - small)

PourAction == SmallToBig \/ BigToSmall

Next == \/ FillSmallJug
        \/ FillBigJug
        \/ EmptySmallJug
        \/ EmptyBigJug
        \/ PourAction

Spec == Init /\ [][Next]_vars

HasFour == big = 4

(* Always TRUE when checked as an invariant; it records that a state with
   big = 4 was reached. *)
_POSSIBLE == HasFour => TLCSet(2, TRUE)

(* Postcondition, evaluated after model checking completes. *)
PossibleCounts ==
    /\ TLCGet(2) = TRUE
    /\ TLCGet("stats").distinct = 16
    /\ TLCGet("stats").generated >= TLCGet("stats").distinct
    /\ TLCGet(1) > 0
=============================================================================