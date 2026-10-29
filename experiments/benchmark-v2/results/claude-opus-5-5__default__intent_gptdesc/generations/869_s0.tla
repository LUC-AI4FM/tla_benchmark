------------------------------ MODULE SingleLaneBridge ------------------------------
(***************************************************************************)
(* Single-lane bridge traffic control.                                     *)
(*                                                                         *)
(* The road is the sequence of positions 1..MaxPos. The bridge is the      *)
(* contiguous segment BridgeStart..BridgeEnd. The approach roads on either *)
(* side of the bridge have two lanes, one per travel direction. The bridge *)
(* has a single lane shared by both directions.                            *)
(*                                                                         *)
(* Left cars start on the left and travel rightwards (positions increase). *)
(* Right cars start on the right and travel leftwards (positions decrease).*)
(*                                                                         *)
(* Position 0 (Outside) means the car is not on the road. A car is either  *)
(* waiting to enter, or it has left the far end and recirculates to its    *)
(* own side, so it attempts to cross again.                                *)
(*                                                                         *)
(* A "cell" is a physical slot. On the bridge, the cell is identified only *)
(* by the position, because the bridge has a single lane. Off the bridge,  *)
(* the cell is identified by the position and the direction lane.          *)
(*                                                                         *)
(* Protocol: a car waiting at the bridge entry may enter only if both of   *)
(* the following hold:                                                     *)
(*   (a) no opposing car is on the bridge, and                             *)
(*   (b) either it is its side's turn, or no opposing car is waiting.      *)
(* Every entry hands the turn to the other side. When both sides contend,  *)
(* access therefore alternates.                                            *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS LeftCars,     \* set of distinct vehicles starting on the left side
          RightCars,    \* set of distinct vehicles starting on the right side
          MaxPos,       \* length of the road (positions 1..MaxPos)
          BridgeStart,  \* first position of the bridge segment
          BridgeEnd     \* last position of the bridge segment

ASSUME LeftCars \cap RightCars = {}
ASSUME IsFiniteSet(LeftCars) /\ IsFiniteSet(RightCars)
ASSUME LeftCars \cup RightCars # {}
ASSUME MaxPos \in Nat /\ BridgeStart \in Nat /\ BridgeEnd \in Nat
ASSUME 1 < BridgeStart /\ BridgeStart <= BridgeEnd /\ BridgeEnd < MaxPos

VARIABLES pos,   \* pos[c] \in 0..MaxPos ; 0 = Outside the road
          turn   \* side that has priority at the bridge when both contend

vars == <<pos, turn>>

-----------------------------------------------------------------------------
Cars      == LeftCars \cup RightCars
Positions == 1..MaxPos
Bridge    == BridgeStart..BridgeEnd
Outside   == 0
Sides     == {"L", "R"}

Side(c)      == IF c \in LeftCars THEN "L" ELSE "R"
Other(s)     == IF s = "L" THEN "R" ELSE "L"
SideCars(s)  == IF s = "L" THEN LeftCars ELSE RightCars

StartPos(c)  == IF c \in LeftCars THEN 1 ELSE MaxPos
LastPos(c)   == IF c \in LeftCars THEN MaxPos ELSE 1
Step(c)      == IF c \in LeftCars THEN pos[c] + 1 ELSE pos[c] - 1

\* Position just before the bridge for side s (where vehicles wait).
EntryPos(s)  == IF s = "L" THEN BridgeStart - 1 ELSE BridgeEnd + 1
\* Position just after the bridge for side s.
ExitPos(s)   == EntryPos(Other(s))

OnRoad(c)    == pos[c] \in Positions
OnBridge(c)  == pos[c] \in Bridge
AtEntry(c)   == pos[c] = EntryPos(Side(c))

\* Physical cell a car c would occupy at position p.
Cell(c, p)   == IF p \in Bridge THEN <<"B", p>> ELSE <<Side(c), p>>

\* Cell for car c at position q is not occupied by any other car.
Free(c, q)   == \A d \in Cars \ {c} : OnRoad(d) => Cell(d, pos[d]) # Cell(c, q)

SideOnBridge(s) == \E d \in SideCars(s) : OnBridge(d)
SideWaiting(s)  == \E d \in SideCars(s) : AtEntry(d)

MayEnterBridge(c) ==
    LET s == Side(c) IN
    /\ ~SideOnBridge(Other(s))
    /\ \/ turn = s
       \/ ~SideWaiting(Other(s))

-----------------------------------------------------------------------------
Init ==
    /\ pos  = [c \in Cars |-> Outside]
    /\ turn \in Sides

\* Vehicle enters the road at its starting end.
Arrive(c) ==
    /\ pos[c] = Outside
    /\ Free(c, StartPos(c))
    /\ pos'  = [pos EXCEPT ![c] = StartPos(c)]
    /\ UNCHANGED turn

\* Vehicle moves one position forward (not crossing onto the bridge).
Advance(c) ==
    /\ OnRoad(c)
    /\ pos[c] # LastPos(c)
    /\ ~AtEntry(c)
    /\ Free(c, Step(c))
    /\ pos'  = [pos EXCEPT ![c] = Step(c)]
    /\ UNCHANGED turn

\* Vehicle at the bridge entry moves onto the bridge according to protocol.
EnterBridge(c) ==
    /\ AtEntry(c)
    /\ MayEnterBridge(c)
    /\ Free(c, Step(c))
    /\ pos'  = [pos EXCEPT ![c] = Step(c)]
    /\ turn' = Other(Side(c))

\* Vehicle leaves the road at the far end and recirculates.
Depart(c) ==
    /\ pos[c] = LastPos(c)
    /\ pos'  = [pos EXCEPT ![c] = Outside]
    /\ UNCHANGED turn

Move(c) == Arrive(c) \/ Advance(c) \/ EnterBridge(c) \/ Depart(c)

Next == \E c \in Cars : Move(c)

\* Strong fairness per vehicle: a vehicle that is repeatedly able to move
\* (it continuously attempts to progress) eventually does so.
Fairness == \A c \in Cars : SF_vars(Move(c))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety and boundedness invariants *)

TypeOK ==
    /\ pos  \in [Cars -> {Outside} \cup Positions]
    /\ turn \in Sides

\* (2) Boundedness: every position lies within the road domain.
Bounded == \A c \in Cars : pos[c] \in {Outside} \cup Positions

\* (1a) No physical position is occupied by more than one vehicle.
NoCollision ==
    \A c, d \in Cars :
        (c # d /\ OnRoad(c) /\ OnRoad(d)) => Cell(c, pos[c]) # Cell(d, pos[d])

\* No two vehicles ever share a bridge position.
NoSharedBridgePos ==
    \A c, d \in Cars : (c # d /\ OnBridge(c) /\ OnBridge(d)) => pos[c] # pos[d]

\* (1b) Opposing-direction vehicles never coexist on the bridge.
BridgeExclusion == ~(SideOnBridge("L") /\ SideOnBridge("R"))

Safety == TypeOK /\ Bounded /\ NoCollision /\ NoSharedBridgePos /\ BridgeExclusion

-----------------------------------------------------------------------------
(* Liveness properties *)

\* No deadlock: some vehicle can always move.
DeadlockFreedom == [](ENABLED Next)

\* Waiting vehicles at either entry eventually get onto the bridge.
WaitingEventuallyEnters ==
    \A c \in Cars : AtEntry(c) ~> OnBridge(c)

\* If a side has a waiting vehicle, some vehicle of that side eventually enters.
SideProgress ==
    \A s \in Sides : SideWaiting(s) ~> SideOnBridge(s)

\* (3) Progress: every vehicle eventually reaches the bridge ...
EventuallyReachBridge ==
    \A c \in Cars : pos[c] = Outside ~> OnBridge(c)

\* ... and then leaves it on the far side.
EventuallyLeaveBridge ==
    \A c \in Cars : OnBridge(c) ~> (pos[c] = ExitPos(Side(c)))

\* No starvation / no livelock: every vehicle crosses infinitely often.
NoStarvation == \A c \in Cars : []<>OnBridge(c)

Liveness ==
    /\ WaitingEventuallyEnters
    /\ SideProgress
    /\ EventuallyReachBridge
    /\ EventuallyLeaveBridge
    /\ NoStarvation

-----------------------------------------------------------------------------
THEOREM Spec => []Safety
THEOREM Spec => DeadlockFreedom
THEOREM Spec => Liveness
=============================================================================