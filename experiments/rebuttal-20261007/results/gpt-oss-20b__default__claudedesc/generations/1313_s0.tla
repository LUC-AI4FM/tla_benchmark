MODULE DieHard
EXTENDS Naturals

CONSTANT smallCap = 3, bigCap = 5

VARIABLES small, big, counter

Init ==
    /\ small = 0
    /\ big = 0
    /\ counter = 0

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

SmallToBig ==
    LET transfer == Min(small, bigCap - big) IN
    /\ small' = small - transfer
    /\ big'   = big + transfer
    /\ counter' = counter

BigToSmall ==
    LET transfer == Min(big, smallCap - small) IN
    /\ big'   = big - transfer
    /\ small' = small + transfer
    /\ counter' = counter

Next ==
    \/ FillSmall
    \/ FillBig
    \/ EmptySmall
    \/ EmptyBig
    \/ SmallToBig
    \/ BigToSmall

TypeOK ==
    /\ small \in 0..smallCap
    /\ big   \in 0..bigCap

HasFour == big = 4

PourAction == (small' != small) /\ (big' != big)

Spec == Init /\ [][Next]_<<small, big, counter>> /\ []TypeOK

Postcondition == counter = 128

(* TLC instrumentation *)
HasFour_Possible   == HasFour _POSSIBLE
PourAction_Possible == PourAction _POSSIBLE