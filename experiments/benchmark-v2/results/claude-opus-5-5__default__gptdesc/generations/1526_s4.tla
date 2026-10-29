------------------------------- MODULE MC -------------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* Model values for the individual cars
CONSTANTS r1, r2, l1, l2

ASSUME Cardinality({r1, r2, l1, l2}) = 4

\* ---------------------------------------------------------------------
\* Model parameterization (explicit set enumerations)
\* ---------------------------------------------------------------------
CarsRight == {r1, r2}
CarsLeft  == {l1, l2}
Bridge    == {4, 5}
Positions == {1, 2, 3, 4, 5, 6, 7, 8}

\* ---------------------------------------------------------------------
\* Single-lane bridge system
\* ---------------------------------------------------------------------
VARIABLES Location, WaitingBeforeBridge

vars == <<Location, WaitingBeforeBridge>>

Cars == CarsRight \cup CarsLeft

Min(S) == CHOOSE x \in S : \A y \in S : x <= y
Max(S) == CHOOSE x \in S : \A y \in S : x >= y

MinPos == Min(Positions)
MaxPos == Max(Positions)

\* Cars that drive in the same direction as c
SameDir(c) == IF c \in CarsRight THEN CarsRight ELSE CarsLeft
\* Cars that drive in the opposite direction of c
OppDir(c)  == IF c \in CarsRight THEN CarsLeft ELSE CarsRight

\* Cars on the right drive leftwards (decreasing positions),
\* cars on the left drive rightwards (increasing positions); the road is circular.
NextLoc(c) ==
    IF c \in CarsRight
    THEN IF Location[c] = MinPos THEN MaxPos ELSE Location[c] - 1
    ELSE IF Location[c] = MaxPos THEN MinPos ELSE Location[c] + 1

\* Position directly in front of the bridge for car c
EntryPos(c) ==
    IF c \in CarsRight THEN Max(Bridge) + 1 ELSE Min(Bridge) - 1

\* Position c' is free of cars driving in the same direction (no overtaking)
FreeAhead(c) == ~\E d \in SameDir(c) \ {c} : Location[d] = NextLoc(c)

TypeOK ==
    /\ Location \in [Cars -> Positions]
    /\ WaitingBeforeBridge \in Seq(Cars)

Init ==
    /\ Location = [c \in Cars |->
                      CASE c = r1 -> 8
                        [] c = r2 -> 7
                        [] c = l1 -> 1
                        [] c = l2 -> 2]
    /\ WaitingBeforeBridge = <<>>

\* Move along the road outside the bridge (including leaving the bridge)
Move(c) ==
    /\ NextLoc(c) \notin Bridge
    /\ FreeAhead(c)
    /\ Location' = [Location EXCEPT ![c] = NextLoc(c)]
    /\ WaitingBeforeBridge' =
           IF NextLoc(c) = EntryPos(c)
           THEN Append(WaitingBeforeBridge, c)
           ELSE WaitingBeforeBridge

\* Enter the bridge: must be first in the queue and no oncoming car on the bridge
EnterBridge(c) ==
    /\ Location[c] \notin Bridge
    /\ NextLoc(c) \in Bridge
    /\ WaitingBeforeBridge /= <<>>
    /\ Head(WaitingBeforeBridge) = c
    /\ \A d \in OppDir(c) : Location[d] \notin Bridge
    /\ FreeAhead(c)
    /\ Location' = [Location EXCEPT ![c] = NextLoc(c)]
    /\ WaitingBeforeBridge' = Tail(WaitingBeforeBridge)

\* Move forward while on the bridge
MoveOnBridge(c) ==
    /\ Location[c] \in Bridge
    /\ NextLoc(c) \in Bridge
    /\ FreeAhead(c)
    /\ Location' = [Location EXCEPT ![c] = NextLoc(c)]
    /\ UNCHANGED WaitingBeforeBridge

CarAction(c) == Move(c) \/ EnterBridge(c) \/ MoveOnBridge(c)

Next == \E c \in Cars : CarAction(c)

Fairness == \A c \in Cars : SF_vars(CarAction(c))

Spec == Init /\ [][Next]_vars /\ Fairness

\* ---------------------------------------------------------------------
\* Safety invariants
\* ---------------------------------------------------------------------
\* Never cars from both directions on the bridge at the same time
NoOpposingCarsOnBridge ==
    ~\E a \in CarsRight, b \in CarsLeft :
        Location[a] \in Bridge /\ Location[b] \in Bridge

\* No two cars driving in the same direction occupy the same position
NoCollision ==
    \A a, b \in Cars :
        (a /= b /\ SameDir(a) = SameDir(b)) => Location[a] /= Location[b]

\* ---------------------------------------------------------------------
\* Liveness property
\* ---------------------------------------------------------------------
CarsInfOftenOnBridge ==
    \A car \in CarsRight : []<>(Location[car] \in Bridge)

=============================================================================