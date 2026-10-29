------------------------------- MODULE MC -------------------------------
EXTENDS Naturals, FiniteSets, TLC

(***************************************************************************)
(* Model parameters for the single-lane bridge system.                     *)
(***************************************************************************)
CarsRight == {"r1", "r2"}

CarsLeft == {"l1", "l2"}

Bridge == {4, 5, 6}

Positions == {1, 2, 3, 4, 5, 6, 7, 8}

Cars == CarsRight \cup CarsLeft

VARIABLES Location

vars == <<Location>>

(***************************************************************************)
(* Right cars travel from position 8 towards 1; left cars travel from     *)
(* position 1 towards 8.  After leaving the far end, a car wraps around to *)
(* its starting side, so cars can cross the bridge again and again.        *)
(***************************************************************************)
StartPos(c) == IF c \in CarsRight THEN 8 ELSE 1

NextPos(c) ==
    IF c \in CarsRight
       THEN IF Location[c] = 1 THEN 8 ELSE Location[c] - 1
       ELSE IF Location[c] = 8 THEN 1 ELSE Location[c] + 1

CarsOnBridge == { c \in Cars : Location[c] \in Bridge }

Opposite(c) == IF c \in CarsRight THEN CarsLeft ELSE CarsRight

\* A position on the bridge can hold at most one car.
NextPosFree(c) ==
    NextPos(c) \notin Bridge
    \/ \A d \in Cars : Location[d] # NextPos(c)

\* A car may enter the bridge only if no car of the opposite direction is on it.
MayEnter(c) ==
    (Location[c] \notin Bridge /\ NextPos(c) \in Bridge)
        => \A d \in Opposite(c) : Location[d] \notin Bridge

TypeOK == Location \in [Cars -> Positions]

Init == Location = [c \in Cars |-> StartPos(c)]

Move(c) ==
    /\ NextPosFree(c)
    /\ MayEnter(c)
    /\ Location' = [Location EXCEPT ![c] = NextPos(c)]

Next == \E c \in Cars : Move(c)

Spec == Init /\ [][Next]_vars /\ \A c \in Cars : WF_vars(Move(c))

(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)
\* Cars travelling in opposite directions are never on the bridge together.
NoOppositeOnBridge ==
    ~ ( (\E r \in CarsRight : Location[r] \in Bridge)
        /\ (\E l \in CarsLeft : Location[l] \in Bridge) )

\* No two cars share a bridge position.
NoCollision ==
    \A c, d \in Cars :
        (c # d /\ Location[c] \in Bridge) => Location[c] # Location[d]

Safety == TypeOK /\ NoOppositeOnBridge /\ NoCollision

(***************************************************************************)
(* Liveness property                                                       *)
(***************************************************************************)
CarsInfOftenOnBridge == \A car \in CarsRight : []<>(Location[car] \in Bridge)

=============================================================================