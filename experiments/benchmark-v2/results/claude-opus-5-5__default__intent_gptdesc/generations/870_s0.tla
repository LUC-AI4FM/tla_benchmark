------------------------------ MODULE SingleLaneBridge ------------------------------
(***************************************************************************)
(* A single-lane bridge crossed by cars from two opposite directions.     *)
(*                                                                         *)
(* Positions are the integers 1..Total, laid out left to right:           *)
(*                                                                         *)
(*   1 .. ApproachLen                    : left-side road                  *)
(*   BridgeStart .. BridgeEnd            : bridge                          *)
(*   BridgeEnd+1 .. Total                : right-side road                 *)
(*                                                                         *)
(* Right-bound cars travel from position 1 towards Total (step +1).       *)
(* Left-bound cars travel from position Total towards 1 (step -1).        *)
(* Each car approaches along its road, reaches the bridge entrance (the   *)
(* position next to the bridge), and joins a FIFO waiting queue there.    *)
(* Only the car at the head of the queue may enter the bridge. It may     *)
(* enter only if:                                                          *)
(*   - no car going the opposite way is on the bridge,                    *)
(*   - the first bridge position in its direction is free, and            *)
(*   - the bridge is below capacity.                                       *)
(* On the bridge cars step forward only into free positions. They leave   *)
(* at the far end and drive on to the far end of the road. There they     *)
(* "recycle" back to their starting end, which models an endless stream   *)
(* of traffic. Cars may share road (non-bridge) positions; bridge         *)
(* positions hold at most one car.                                         *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    RightCars,     \* cars travelling left-to-right
    LeftCars,      \* cars travelling right-to-left
    ApproachLen,   \* number of road positions on each side of the bridge
    BridgeLen,     \* number of positions on the bridge
    Capacity       \* maximum number of cars allowed on the bridge

Cars == RightCars \cup LeftCars

ASSUME
    /\ RightCars \cap LeftCars = {}
    /\ Cars # {}
    /\ ApproachLen \in Nat /\ ApproachLen >= 2
    /\ BridgeLen \in Nat /\ BridgeLen >= 1
    /\ Capacity \in 1..BridgeLen

BridgeStart == ApproachLen + 1
BridgeEnd   == ApproachLen + BridgeLen
Total       == 2 * ApproachLen + BridgeLen
Positions   == 1..Total
BridgePos   == BridgeStart..BridgeEnd

VARIABLES
    loc,       \* loc[c] : current position of car c
    waiting    \* FIFO queue of cars waiting at their bridge entrance

vars == <<loc, waiting>>

-----------------------------------------------------------------------------
(* Direction-dependent geometry *)

Dir(c)       == IF c \in RightCars THEN 1 ELSE -1
Start(c)     == IF c \in RightCars THEN 1 ELSE Total
Final(c)     == IF c \in RightCars THEN Total ELSE 1
Entrance(c)  == IF c \in RightCars THEN ApproachLen ELSE BridgeEnd + 1
EntryPos(c)  == IF c \in RightCars THEN BridgeStart ELSE BridgeEnd
LastPos(c)   == IF c \in RightCars THEN BridgeEnd ELSE BridgeStart

OnBridge(c)  == loc[c] \in BridgePos
Before(c)    == IF c \in RightCars THEN loc[c] < BridgeStart ELSE loc[c] > BridgeEnd
After(c)     == IF c \in RightCars THEN loc[c] > BridgeEnd   ELSE loc[c] < BridgeStart

CarsOnBridge == {c \in Cars : OnBridge(c)}
Occupied(p)  == \E d \in Cars : d \in CarsOnBridge /\ loc[d] = p
InQueue(c)   == \E i \in 1..Len(waiting) : waiting[i] = c

-----------------------------------------------------------------------------
(* Initial state: every car is off the bridge at its starting end. *)

Init ==
    /\ loc = [c \in Cars |-> Start(c)]
    /\ waiting = << >>

-----------------------------------------------------------------------------
(* Actions *)

\* Step forward along the approach road; join the queue on reaching the entrance.
MoveApproach(c) ==
    /\ Before(c)
    /\ loc[c] # Entrance(c)
    /\ loc' = [loc EXCEPT ![c] = loc[c] + Dir(c)]
    /\ waiting' = IF loc[c] + Dir(c) = Entrance(c)
                     THEN Append(waiting, c)
                     ELSE waiting

\* Head of the queue enters the bridge when this is safe.
Enter(c) ==
    /\ waiting # << >>
    /\ Head(waiting) = c
    /\ loc[c] = Entrance(c)
    /\ \A d \in CarsOnBridge : Dir(d) = Dir(c)
    /\ ~Occupied(EntryPos(c))
    /\ Cardinality(CarsOnBridge) < Capacity
    /\ loc' = [loc EXCEPT ![c] = EntryPos(c)]
    /\ waiting' = Tail(waiting)

\* Step forward on the bridge into a free position.
MoveOnBridge(c) ==
    /\ OnBridge(c)
    /\ loc[c] # LastPos(c)
    /\ ~Occupied(loc[c] + Dir(c))
    /\ loc' = [loc EXCEPT ![c] = loc[c] + Dir(c)]
    /\ UNCHANGED waiting

\* Leave the bridge at the far end.
Leave(c) ==
    /\ OnBridge(c)
    /\ loc[c] = LastPos(c)
    /\ loc' = [loc EXCEPT ![c] = loc[c] + Dir(c)]
    /\ UNCHANGED waiting

\* Drive on along the far-side road.
MoveAfter(c) ==
    /\ After(c)
    /\ loc[c] # Final(c)
    /\ loc' = [loc EXCEPT ![c] = loc[c] + Dir(c)]
    /\ UNCHANGED waiting

\* Leave the system at the far end and reappear at the starting end.
Recycle(c) ==
    /\ loc[c] = Final(c)
    /\ loc' = [loc EXCEPT ![c] = Start(c)]
    /\ UNCHANGED waiting

Step(c) ==
    \/ MoveApproach(c)
    \/ Enter(c)
    \/ MoveOnBridge(c)
    \/ Leave(c)
    \/ MoveAfter(c)
    \/ Recycle(c)

Next == \E c \in Cars : Step(c)

(* Fairness: no enabled move of any car can be deferred forever. *)
Fairness == \A c \in Cars : WF_vars(Step(c))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety invariants *)

TypeOK ==
    /\ loc \in [Cars -> Positions]
    /\ waiting \in Seq(Cars)

\* No two cars travelling in opposite directions are on the bridge together.
NoOppositeOnBridge ==
    \A c, d \in CarsOnBridge : Dir(c) = Dir(d)

\* No two cars occupy the same bridge position.
NoCollision ==
    \A c, d \in CarsOnBridge : c # d => loc[c] # loc[d]

\* The bridge never holds more cars than its capacity.
CapacityOK ==
    Cardinality(CarsOnBridge) <= Capacity

\* The queue holds exactly the cars waiting at their entrance, each once.
QueueConsistent ==
    /\ \A c \in Cars : InQueue(c) <=> loc[c] = Entrance(c) /\ Before(c)
    /\ \A i, j \in 1..Len(waiting) : i # j => waiting[i] # waiting[j]

Safety == NoOppositeOnBridge /\ NoCollision /\ CapacityOK

-----------------------------------------------------------------------------
(* Liveness properties *)

\* Every car that reaches its bridge entrance eventually enters the bridge.
EventuallyEnter ==
    \A c \in Cars : (loc[c] = Entrance(c) /\ Before(c)) ~> OnBridge(c)

\* Every car on the bridge eventually leaves it on the far side.
EventuallyExit ==
    \A c \in Cars : OnBridge(c) ~> After(c)

\* Every approaching car eventually crosses (no permanent starvation).
NoStarvation ==
    \A c \in Cars : Before(c) ~> After(c)

\* Every car crosses the bridge infinitely often.
CrossesInfinitelyOften ==
    \A c \in Cars : []<>OnBridge(c)

-----------------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ Safety /\ QueueConsistent)
THEOREM Spec => EventuallyEnter /\ EventuallyExit /\ NoStarvation

=============================================================================