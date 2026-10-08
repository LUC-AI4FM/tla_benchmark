------------------------------ MODULE DieHardJug ------------------------------
EXTENDS Naturals, TLC

CONSTANTS smallCap, bigCap

VARIABLES small, big, counter

(* Initial state *)
Init == /\ small = 0
        /\ big = 0
        /\ counter = 0

(* Actions *)
FillSmall ==
    /\ small' = smallCap
    /\ big'   = big
    /\ counter' = counter + smallCap

FillBig ==
    /\ big'   = bigCap
    /\ small' = small
    /\ counter' = counter + bigCap

EmptySmall ==
    /\ small' = 0
    /\ big'   = big
    /\ counter' = counter

EmptyBig ==
    /\ big'   = 0
    /\ small' = small
    /\ counter' = counter

PourFromSmallToBig ==
    LET transfer == Min(small, bigCap - big) IN
    /\ small' = small - transfer
    /\ big'   = big + transfer
    /\ counter' = counter

PourFromBigToSmall ==
    LET transfer == Min(big, smallCap - small) IN
    /\ big'   = big - transfer
    /\ small' = small + transfer
    /\ counter' = counter

Stutter ==
    /\ small' = small
    /\ big'   = big
    /\ counter' = counter

Next == \/ FillSmall
        \/ FillBig
        \/ EmptySmall
        \/ EmptyBig
        \/ PourFromSmallToBig
        \/ PourFromBigToSmall
        \/ Stutter

(* Temporal specification *)
Spec == Init /\ [][Next]_<<small, big, counter>> /\ []TypeOK

(* Type invariant *)
TypeOK ==
    /\ 0 <= small <= smallCap
    /\ 0 <= big   <= bigCap

(* Goal predicate *)
HasFour == big = 4

(* Pour action predicate (both jugs change) *)
PourAction == (small' /= small \/ big' /= big)

(* Instrumentation: counter of gallons filled *)
TotalFilled == counter

(* Post-condition asserting total gallons used *)
PostCondition == counter = 128

(* Possible counts instrumentation *)
HasFour_POSSIBLE == /\ big = 4 \* _POSSIBLE
PourAction_POSSIBLE == (small' /= small /\ big' /= big) \* _POSSIBLE

PossibleCounts ==
    /\ HasFour_POSSIBLE   = 8
    /\ PourAction_POSSIBLE = 14

=============================================================================