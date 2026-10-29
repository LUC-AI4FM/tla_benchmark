---------------------------- MODULE SingleLaneBridge ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CarsRight, CarsLeft, Bridge, Positions

VARIABLES Location, WaitingBeforeBridge

vars == <<Location, WaitingBeforeBridge>>

const_1615720459299211000 == {"r1", "r2"}
const_1615720459299212000 == {"l1", "l2"}
const_1615720459299213000 == {4, 5}
const_1615720459299214000 == 1..8

-----------------------------------------------------------------------------

Cars == CarsRight \cup CarsLeft

Min(S) == CHOOSE x \in S : \A y \in S : x <= y
Max(S) == CHOOSE x \in S : \A y \in S : x >= y

SameSide(c) == IF c \in CarsRight THEN CarsRight ELSE CarsLeft
OtherSide(c) == IF c \in CarsRight THEN CarsLeft ELSE CarsRight

\* Right cars travel with increasing positions, left cars with decreasing
\* positions; after reaching the end of the road they return to the start.
NextLocation(c) ==
    IF c \in CarsRight
    THEN IF Location[c] = Max(Positions) THEN Min(Positions) ELSE Location[c] + 1
    ELSE IF Location[c] = Min(Positions) THEN Max(Positions) ELSE Location[c] - 1

CarsInBridge == { c \in Cars : Location[c] \in Bridge }

\* A position is free for car c if no other car going the same way occupies it.
\* (Approach roads are two-lane; only the bridge is single-lane.)
Free(c, p) == \A d \in SameSide(c) \ {c} : Location[d] # p

InQueue(c) == \E i \in 1..Len(WaitingBeforeBridge) : WaitingBeforeBridge[i] = c

AtBridgeEntrance(c) == Location[c] \notin Bridge /\ NextLocation(c) \in Bridge

-----------------------------------------------------------------------------

Init ==
    /\ Location \in { f \in [Cars -> Positions \ Bridge] :
                        \A a, b \in Cars :
                           (a # b /\ SameSide(a) = SameSide(b)) => f[a] # f[b] }
    /\ WaitingBeforeBridge = << >>

\* Ordinary movement: either along the road outside the bridge, or
\* moving forward while on the bridge (including leaving it).
Move(c) ==
    /\ \/ Location[c] \in Bridge
       \/ NextLocation(c) \notin Bridge
    /\ Free(c, NextLocation(c))
    /\ Location' = [Location EXCEPT ![c] = NextLocation(c)]
    /\ UNCHANGED WaitingBeforeBridge

\* A car arriving at the bridge entrance registers in the FIFO queue.
Wait(c) ==
    /\ AtBridgeEntrance(c)
    /\ ~InQueue(c)
    /\ WaitingBeforeBridge' = Append(WaitingBeforeBridge, c)
    /\ UNCHANGED Location

\* Only the head of the queue may enter, and only if no opposite car is on the bridge.
Enter(c) ==
    /\ WaitingBeforeBridge # << >>
    /\ Head(WaitingBeforeBridge) = c
    /\ AtBridgeEntrance(c)
    /\ \A d \in OtherSide(c) : Location[d] \notin Bridge
    /\ Free(c, NextLocation(c))
    /\ Location' = [Location EXCEPT ![c] = NextLocation(c)]
    /\ WaitingBeforeBridge' = Tail(WaitingBeforeBridge)

Next == \E c \in Cars : Move(c) \/ Wait(c) \/ Enter(c)

Fairness ==
    \A c \in Cars :
        /\ WF_vars(Move(c))
        /\ WF_vars(Wait(c))
        /\ WF_vars(Enter(c))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety

TypeOK ==
    /\ Location \in [Cars -> Positions]
    /\ \A i \in 1..Len(WaitingBeforeBridge) : WaitingBeforeBridge[i] \in Cars

NoHeadOnCollision ==
    ~(\E r \in CarsRight, l \in CarsLeft :
         Location[r] \in Bridge /\ Location[l] \in Bridge)

NoPositionConflict ==
    /\ \A a, b \in Cars :
          (a # b /\ SameSide(a) = SameSide(b)) => Location[a] # Location[b]
    /\ \A a, b \in Cars :
          (a # b /\ Location[a] \in Bridge /\ Location[b] \in Bridge)
             => Location[a] # Location[b]

DirectionalExclusivity ==
    \/ CarsInBridge \subseteq CarsRight
    \/ CarsInBridge \subseteq CarsLeft

Invariants ==
    /\ TypeOK
    /\ NoHeadOnCollision
    /\ NoPositionConflict
    /\ DirectionalExclusivity

-----------------------------------------------------------------------------
\* Liveness

CarsInBridgeExitBridge ==
    \A c \in Cars : (Location[c] \in Bridge) ~> (Location[c] \notin Bridge)

CarsEnterBridge ==
    \A c \in Cars : (Location[c] \notin Bridge) ~> (Location[c] \in Bridge)

=============================================================================