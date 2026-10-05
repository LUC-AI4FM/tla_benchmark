---------------------------- MODULE DieHard ----------------------------
EXTENDS Integers, TLC

CONSTANTS Small, Big

VARIABLES small, big, waterUsed

vars == <<small, big, waterUsed>>

TypeOK == 
    /\ small \in 0..Small
    /\ big \in 0..Big
    /\ waterUsed \in Nat

Init ==
    /\ small = 0
    /\ big = 0
    /\ waterUsed = 0

FillSmall ==
    /\ small' = Small
    /\ big' = big
    /\ waterUsed' = waterUsed + (Small - small)

FillBig ==
    /\ big' = Big
    /\ small' = small
    /\ waterUsed' = waterUsed + (Big - big)

EmptySmall ==
    /\ small' = 0
    /\ big' = big
    /\ waterUsed' = waterUsed

EmptyBig ==
    /\ big' = 0
    /\ small' = small
    /\ waterUsed' = waterUsed

SmallToBig ==
    LET amount == IF small + big <= Big THEN small ELSE Big - big
    IN
        /\ small' = small - amount
        /\ big' = big + amount
        /\ waterUsed' = waterUsed

BigToSmall ==
    LET amount == IF small + big <= Small THEN big ELSE Small - small
    IN
        /\ big' = big - amount
        /\ small' = small + amount
        /\ waterUsed' = waterUsed

Next ==
    \/ FillSmall
    \/ FillBig
    \/ EmptySmall
    \/ EmptyBig
    \/ SmallToBig
    \/ BigToSmall

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety Invariants *)

NotFour == big /= 4

BigNeverFour == []NotFour

(* Liveness Properties - checking reachability *)
EventuallyFour == <>(big = 4)

-----------------------------------------------------------------------------
(* TLC Statistics and Inspection Operators *)

StateCount == TLCGet("distinct")

ActionCount == TLCGet("generated")

Diameter == TLCGet("diameter")

-----------------------------------------------------------------------------
(* Predicates for checking state space properties *)

BigHasFour == big = 4

CheckStateSpace == 
    TLCGet("distinct") > 0

ExpectedStatesReached ==
    LET states == TLCGet("distinct")
    IN states >= 1

ExpectedActionsGenerated ==
    LET actions == TLCGet("generated")
    IN actions >= 1

PostCondition ==
    /\ PrintT(<<"Distinct States:", TLCGet("distinct")>>)
    /\ PrintT(<<"Generated States:", TLCGet("generated")>>)
    /\ PrintT(<<"Diameter:", TLCGet("diameter")>>)

-----------------------------------------------------------------------------
(* Alias for state display *)
Alias == [
    small |-> small,
    big |-> big,
    waterUsed |-> waterUsed,
    stateCount |-> TLCGet("distinct")
]

=============================================================================