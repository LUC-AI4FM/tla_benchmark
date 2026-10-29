------------------------------ MODULE SingleLaneBridge ------------------------------
(***************************************************************************)
(* Classic single-lane bridge problem.  Cars from the left (CarsLeft)      *)
(* travel in increasing position order, cars from the right (CarsRight)    *)
(* travel in decreasing position order.  The road wraps around, so cars    *)
(* cross the bridge repeatedly.  The bridge is a contiguous segment of     *)
(* Positions.  Outside the bridge the road has two lanes, one per          *)
(* direction.  On the bridge there is one lane, so cars going in opposite  *)
(* directions may never be on it at the same time.  Cars that reach the    *)
(* position just before the bridge join a FIFO queue.  Only the car at the *)
(* head of the queue may enter, which guarantees that no car waits forever.*)
(*                                                                         *)
(* Model values used for checking:                                         *)
(*   CarsRight = {r1, r2}, CarsLeft = {l1, l2},                            *)
(*   Bridge = {4, 5}, Positions = 1..8                                     *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS CarsRight, CarsLeft, Bridge, Positions

VARIABLES Location, WaitingBeforeBridge

vars == <<Location, WaitingBeforeBridge>>

Cars == CarsRight \union CarsLeft

Min(S) == CHOOSE m \in S : \A p \in S : m <= p
Max(S) == CHOOSE m \in S : \A p \in S : m >= p

StartPos    == Min(Positions)
EndPos      == Max(Positions)
StartBridge == Min(Bridge)
EndBridge   == Max(Bridge)

\* Position where a car waits before entering the bridge
LeftWaitPos  == StartBridge - 1
RightWaitPos == EndBridge + 1

ASSUME /\ CarsRight \cap CarsLeft = {}
       /\ Positions = StartPos..EndPos
       /\ Bridge = StartBridge..EndBridge
       /\ Bridge \subseteq Positions
       /\ StartPos < LeftWaitPos
       /\ RightWaitPos < EndPos

WaitPos(c) == IF c \in CarsLeft THEN LeftWaitPos ELSE RightWaitPos

SameSide(c) == IF c \in CarsLeft THEN CarsLeft ELSE CarsRight

\* Left cars move rightwards, right cars move leftwards, wrapping around.
LMove(pos) == IF pos < EndPos THEN pos + 1 ELSE StartPos
RMove(pos) == IF pos > StartPos THEN pos - 1 ELSE EndPos

NextLocation(c) == IF c \in CarsLeft THEN LMove(Location[c])
                                     ELSE RMove(Location[c])

CarsInBridge == { c \in Cars : Location[c] \in Bridge }

HaveSameDirection(c) ==
    \A x \in CarsInBridge : (x \in CarsLeft) = (c \in CarsLeft)

FreeForAll(p) == \A x \in Cars : Location[x] # p

-----------------------------------------------------------------------------

Init ==
    /\ Location \in [Cars -> Positions \ (Bridge \cup {LeftWaitPos, RightWaitPos})]
    /\ \A c1, c2 \in Cars :
          (c1 # c2 /\ SameSide(c1) = SameSide(c2)) => Location[c1] # Location[c2]
    /\ WaitingBeforeBridge = << >>

\* Car c enters the bridge from its waiting position
EnterBridge(c) ==
    /\ Location[c] \notin Bridge
    /\ NextLocation(c) \in Bridge
    /\ WaitingBeforeBridge # << >>
    /\ Head(WaitingBeforeBridge) = c
    /\ HaveSameDirection(c)
    /\ FreeForAll(NextLocation(c))
    /\ Location' = [Location EXCEPT ![c] = NextLocation(c)]
    /\ WaitingBeforeBridge' = Tail(WaitingBeforeBridge)

\* Car c advances along the bridge
MoveInsideBridge(c) ==
    /\ Location[c] \in Bridge
    /\ NextLocation(c) \in Bridge
    /\ FreeForAll(NextLocation(c))
    /\ Location' = [Location EXCEPT ![c] = NextLocation(c)]
    /\ UNCHANGED WaitingBeforeBridge

\* Car c moves on the two-lane road, possibly leaving the bridge or
\* arriving at the waiting position (where it joins the queue)
MoveOutsideBridge(c) ==
    /\ NextLocation(c) \notin Bridge
    /\ \A x \in SameSide(c) : Location[x] # NextLocation(c)
    /\ Location' = [Location EXCEPT ![c] = NextLocation(c)]
    /\ IF NextLocation(c) = WaitPos(c)
          THEN WaitingBeforeBridge' = Append(WaitingBeforeBridge, c)
          ELSE UNCHANGED WaitingBeforeBridge

Move(c) == EnterBridge(c) \/ MoveInsideBridge(c) \/ MoveOutsideBridge(c)

Next == \E c \in Cars : Move(c)

Fairness == \A c \in Cars : WF_vars(Move(c))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety *)

TypeOK ==
    /\ Location \in [Cars -> Positions]
    /\ WaitingBeforeBridge \in Seq(Cars)

\* Never cars from opposite directions on the bridge at the same time
NoOppositeCarsInBridge ==
    \/ CarsInBridge \subseteq CarsLeft
    \/ CarsInBridge \subseteq CarsRight

\* At most one car per bridge position
NoCollisionInBridge ==
    \A c1, c2 \in CarsInBridge : c1 # c2 => Location[c1] # Location[c2]

\* Cars in the same direction never share a position
NoCollisionSameLane ==
    \A c1, c2 \in Cars :
        (c1 # c2 /\ SameSide(c1) = SameSide(c2)) => Location[c1] # Location[c2]

\* The waiting queue contains each car at most once, and only waiting cars
WaitingConsistent ==
    /\ \A i, j \in 1..Len(WaitingBeforeBridge) :
          i # j => WaitingBeforeBridge[i] # WaitingBeforeBridge[j]
    /\ \A i \in 1..Len(WaitingBeforeBridge) :
          LET c == WaitingBeforeBridge[i] IN Location[c] = WaitPos(c)

Invariants ==
    /\ TypeOK
    /\ NoOppositeCarsInBridge
    /\ NoCollisionInBridge
    /\ NoCollisionSameLane
    /\ WaitingConsistent

-----------------------------------------------------------------------------
(* Liveness *)

\* Every car on the bridge eventually leaves it
CarsInBridgeExitBridge ==
    \A c \in Cars : (Location[c] \in Bridge) ~> (Location[c] \notin Bridge)

\* Every car off the bridge eventually gets onto it
CarsEnterBridge ==
    \A c \in Cars : (Location[c] \notin Bridge) ~> (Location[c] \in Bridge)

THEOREM Spec => []Invariants
=============================================================================