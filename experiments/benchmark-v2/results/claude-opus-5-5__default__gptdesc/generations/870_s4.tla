---------------------------- MODULE SingleLaneBridge ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CarsRight,    \* cars travelling to the right (increasing positions)
          CarsLeft,     \* cars travelling to the left (decreasing positions)
          N,            \* positions are 1..N (road wraps around)
          BridgeStart,  \* first position of the bridge
          BridgeEnd     \* last position of the bridge

ASSUME CarsRight \cap CarsLeft = {}
ASSUME N \in Nat /\ BridgeStart \in Nat /\ BridgeEnd \in Nat
ASSUME 1 < BridgeStart /\ BridgeStart <= BridgeEnd /\ BridgeEnd < N
ASSUME IsFiniteSet(CarsRight) /\ IsFiniteSet(CarsLeft)
ASSUME Cardinality(CarsRight) <= N - (BridgeEnd - BridgeStart + 3)
ASSUME Cardinality(CarsLeft)  <= N - (BridgeEnd - BridgeStart + 3)

VARIABLES Location,            \* Location[c] : current position of car c
          WaitingBeforeBridge  \* FIFO queue of cars waiting to enter the bridge

vars == <<Location, WaitingBeforeBridge>>

Cars      == CarsRight \cup CarsLeft
Positions == 1..N
Bridge    == BridgeStart..BridgeEnd

SameDir(c, d) == (c \in CarsRight) <=> (d \in CarsRight)

\* Position immediately before the bridge for car c
Before(c) == IF c \in CarsRight THEN BridgeStart - 1 ELSE BridgeEnd + 1

\* Next position of car c along its direction (road wraps around)
NextPos(c) ==
    IF c \in CarsRight
    THEN IF Location[c] = N THEN 1 ELSE Location[c] + 1
    ELSE IF Location[c] = 1 THEN N ELSE Location[c] - 1

\* Position p is free for car c: no same-direction car there, and
\* no car at all there if p is on the bridge
Free(c, p) ==
    \A d \in Cars \ {c} :
        /\ SameDir(c, d) => Location[d] # p
        /\ p \in Bridge => Location[d] # p

\* No car travelling in the opposite direction is on the bridge
BridgeClearFor(c) ==
    \A d \in Cars : ~SameDir(c, d) => Location[d] \notin Bridge

-----------------------------------------------------------------------------
TypeOK ==
    /\ Location \in [Cars -> Positions]
    /\ WaitingBeforeBridge \in Seq(Cars)

InitPositions == Positions \ (Bridge \cup {BridgeStart - 1, BridgeEnd + 1})

Init ==
    /\ Location \in [Cars -> InitPositions]
    /\ \A c, d \in Cars : (c # d /\ SameDir(c, d)) => Location[c] # Location[d]
    /\ WaitingBeforeBridge = <<>>

\* Ordinary movement (off the bridge, or along the bridge, or leaving it).
\* A car reaching the position just before the bridge joins the waiting queue.
Move(c) ==
    LET p == NextPos(c) IN
    /\ Location[c] # Before(c)
    /\ Free(c, p)
    /\ Location' = [Location EXCEPT ![c] = p]
    /\ WaitingBeforeBridge' =
          IF p = Before(c) THEN Append(WaitingBeforeBridge, c)
                           ELSE WaitingBeforeBridge

\* The car at the head of the waiting queue enters the bridge when no car
\* travelling in the opposite direction is on the bridge.
Enter(c) ==
    LET p == NextPos(c) IN
    /\ WaitingBeforeBridge # <<>>
    /\ c = Head(WaitingBeforeBridge)
    /\ Location[c] = Before(c)
    /\ BridgeClearFor(c)
    /\ Free(c, p)
    /\ Location' = [Location EXCEPT ![c] = p]
    /\ WaitingBeforeBridge' = Tail(WaitingBeforeBridge)

Next == \E c \in Cars : Move(c) \/ Enter(c)

Fairness == \A c \in Cars : WF_vars(Move(c)) /\ WF_vars(Enter(c))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety

\* Cars going in opposite directions are never on the bridge simultaneously
BridgeSafety ==
    ~ \E r \in CarsRight, l \in CarsLeft :
        Location[r] \in Bridge /\ Location[l] \in Bridge

\* No two cars occupy the same bridge position; no two same-direction cars
\* occupy the same position anywhere
NoCollision ==
    \A c, d \in Cars :
        c # d =>
            /\ Location[c] \in Bridge => Location[c] # Location[d]
            /\ SameDir(c, d) => Location[c] # Location[d]

\* Waiting cars are exactly those just before the bridge, each queued once
WaitingOK ==
    /\ \A i \in 1..Len(WaitingBeforeBridge) :
          Location[WaitingBeforeBridge[i]] = Before(WaitingBeforeBridge[i])
    /\ \A i, j \in 1..Len(WaitingBeforeBridge) :
          i # j => WaitingBeforeBridge[i] # WaitingBeforeBridge[j]

Invariants == TypeOK /\ BridgeSafety /\ NoCollision /\ WaitingOK

\* Liveness

CarsEnterBridge ==
    \A c \in Cars : (Location[c] \notin Bridge) ~> (Location[c] \in Bridge)

CarsExitBridge ==
    \A c \in Cars : (Location[c] \in Bridge) ~> (Location[c] \notin Bridge)

THEOREM Spec => [](TypeOK /\ BridgeSafety /\ NoCollision /\ WaitingOK)
THEOREM Spec => CarsEnterBridge /\ CarsExitBridge
=============================================================================