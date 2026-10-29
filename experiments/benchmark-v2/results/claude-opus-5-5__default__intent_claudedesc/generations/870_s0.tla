---------------------------- MODULE SingleLaneBridge ----------------------------
(***************************************************************************)
(* A single-lane bridge traffic control system.                            *)
(*                                                                         *)
(* The road is circular, with positions 1..N. The bridge is the contiguous *)
(* segment BridgeStart..BridgeEnd.                                         *)
(*                                                                         *)
(* CarsRight travel in increasing position order and wrap from N to 1.     *)
(* CarsLeft travel in decreasing position order and wrap from 1 to N.      *)
(*                                                                         *)
(* Off the bridge the road has two lanes, so cars may share a position     *)
(* there. On the bridge every position holds at most one car.              *)
(*                                                                         *)
(* A car joins a FIFO waiting queue when it arrives at the approach        *)
(* position just before the bridge. Only the car at the head of the queue  *)
(* may enter. It enters only when every car on the bridge travels in its   *)
(* direction and the entry position is free.                               *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    CarsRight,      \* cars travelling in increasing position order
    CarsLeft,       \* cars travelling in decreasing position order
    N,              \* number of positions on the circular road
    BridgeStart,    \* first (lowest) bridge position
    BridgeEnd       \* last (highest) bridge position

ASSUME CarsRight \cap CarsLeft = {}
ASSUME N \in Nat /\ BridgeStart \in Nat /\ BridgeEnd \in Nat
ASSUME 1 < BridgeStart /\ BridgeStart <= BridgeEnd /\ BridgeEnd < N

VARIABLES
    Location,       \* Location[c] : current position of car c
    Waiting         \* FIFO queue of cars waiting to enter the bridge

vars == <<Location, Waiting>>

-----------------------------------------------------------------------------
Cars      == CarsRight \cup CarsLeft
Positions == 1..N
Bridge    == BridgeStart..BridgeEnd

SameDirection(c) == IF c \in CarsRight THEN CarsRight ELSE CarsLeft

\* Position immediately before the bridge, for a car of c's direction
Approach(c) == IF c \in CarsRight THEN BridgeStart - 1 ELSE BridgeEnd + 1

\* First bridge position entered, for a car of c's direction
EntryPos(c) == IF c \in CarsRight THEN BridgeStart ELSE BridgeEnd

\* Next position along c's direction of travel (circular road)
NextPos(c) ==
    IF c \in CarsRight
        THEN IF Location[c] = N THEN 1 ELSE Location[c] + 1
        ELSE IF Location[c] = 1 THEN N ELSE Location[c] - 1

CarsOnBridge == { c \in Cars : Location[c] \in Bridge }

Occupied(p) == \E d \in Cars : Location[d] = p

InQueue(c) == \E i \in 1..Len(Waiting) : Waiting[i] = c

-----------------------------------------------------------------------------
TypeOK ==
    /\ Location \in [Cars -> Positions]
    /\ Waiting \in Seq(Cars)

Init ==
    /\ Location \in { f \in [Cars -> Positions \ Bridge] :
                         \A c \in Cars : f[c] # Approach(c) }
    /\ Waiting = << >>

(***************************************************************************)
(* Ordinary movement along the road.                                       *)
(*                                                                         *)
(* A car at its approach position cannot use this action; it must enter    *)
(* through the bridge entry protocol. A move onto a bridge position, made  *)
(* while already on the bridge, requires that position to be free. A car   *)
(* that reaches its approach position joins the end of the queue.          *)
(***************************************************************************)
Move(c) ==
    /\ Location[c] # Approach(c)
    /\ LET p == NextPos(c) IN
         /\ (p \in Bridge) => ~Occupied(p)
         /\ Location' = [Location EXCEPT ![c] = p]
         /\ Waiting' = IF p = Approach(c) THEN Append(Waiting, c) ELSE Waiting

(***************************************************************************)
(* Bridge entry protocol.                                                  *)
(*                                                                         *)
(* The head of the FIFO queue enters when three conditions hold:           *)
(*   - it is at its approach position,                                     *)
(*   - the bridge is empty or holds only same-direction cars,              *)
(*   - the entry position is unoccupied.                                   *)
(***************************************************************************)
Enter(c) ==
    /\ Waiting # << >>
    /\ Head(Waiting) = c
    /\ Location[c] = Approach(c)
    /\ CarsOnBridge \subseteq SameDirection(c)
    /\ ~Occupied(EntryPos(c))
    /\ Location' = [Location EXCEPT ![c] = EntryPos(c)]
    /\ Waiting' = Tail(Waiting)

Next == \E c \in Cars : Move(c) \/ Enter(c)

Fairness == \A c \in Cars : WF_vars(Move(c)) /\ WF_vars(Enter(c))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

\* No two cars occupy the same position on the bridge
NoCollision ==
    \A c, d \in Cars :
        (c # d /\ Location[c] \in Bridge) => Location[c] # Location[d]

\* Cars travelling in opposite directions are never on the bridge together
NoHeadOnConflict ==
    ~(\E r \in CarsRight, l \in CarsLeft :
          Location[r] \in Bridge /\ Location[l] \in Bridge)

\* The number of cars on the bridge never exceeds its length
CapacityLimit == Cardinality(CarsOnBridge) <= Cardinality(Bridge)

\* Queue consistency: queued cars are exactly those at their approach position
QueueConsistent ==
    /\ \A c \in Cars : InQueue(c) <=> Location[c] = Approach(c)
    /\ \A i, j \in 1..Len(Waiting) : i # j => Waiting[i] # Waiting[j]

Safety == TypeOK /\ NoCollision /\ NoHeadOnConflict /\ CapacityLimit /\ QueueConsistent

-----------------------------------------------------------------------------
(* Liveness properties *)

\* Every car that enters the bridge eventually exits it
BridgeExit ==
    \A c \in Cars : (Location[c] \in Bridge) ~> (Location[c] \notin Bridge)

\* Every waiting car eventually gets onto the bridge (no starvation)
WaitingLeadsToEntry ==
    \A c \in Cars : InQueue(c) ~> (Location[c] \in Bridge)

\* Every car crosses the bridge infinitely often
BridgeEntry ==
    \A c \in Cars : []<>(Location[c] \in Bridge)

THEOREM Spec => []Safety
THEOREM Spec => BridgeExit /\ WaitingLeadsToEntry /\ BridgeEntry
=============================================================================