--------------------------- MODULE SingleLaneBridge ---------------------------
(***************************************************************************)
(* Single-lane bridge traffic control.                                     *)
(*                                                                         *)
(* Positions is a contiguous range of integers, and Bridge is a contiguous *)
(* sub-range strictly inside it.                                           *)
(*                                                                         *)
(*  - Left cars arrive from the left. They enter the road at the leftmost  *)
(*    position, drive right through the left approach, cross the bridge,   *)
(*    and leave the system after the last bridge position.                 *)
(*  - Right cars do the same in the mirror direction.                      *)
(*                                                                         *)
(* After leaving, a car is "off road". It may later come back from its     *)
(* own side, so traffic goes on forever.                                   *)
(*                                                                         *)
(* Cars waiting just before the bridge join a FIFO queue. Only the car at  *)
(* the head of the queue may enter the bridge, and only when no car from   *)
(* the opposite side is on the bridge. Several cars going the same         *)
(* direction may be on the bridge at once. The FIFO order, together with   *)
(* strong fairness, rules out starvation.                                  *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS CarsLeft,    \* cars approaching from the left side
          CarsRight,   \* cars approaching from the right side
          Bridge,      \* positions that constitute the bridge
          Positions    \* all positions in the system

VARIABLES loc,         \* loc[c] : current position of car c (or OffRoad)
          waiting      \* FIFO queue of cars waiting in front of the bridge

vars == <<loc, waiting>>

Cars == CarsLeft \cup CarsRight

SetMin(S) == CHOOSE x \in S : \A y \in S : x <= y
SetMax(S) == CHOOSE x \in S : \A y \in S : x >= y

MinPos      == SetMin(Positions)
MaxPos      == SetMax(Positions)
BridgeStart == SetMin(Bridge)
BridgeEnd   == SetMax(Bridge)

ASSUME /\ CarsLeft \cap CarsRight = {}
       /\ IsFiniteSet(Positions) /\ Positions # {} /\ Positions \subseteq Int
       /\ Bridge # {} /\ Bridge \subseteq Positions
       /\ Positions = MinPos..MaxPos
       /\ Bridge = BridgeStart..BridgeEnd
       /\ MinPos < BridgeStart
       /\ BridgeEnd < MaxPos

\* A location that is not on the road (a car outside the system).
OffRoad == MinPos - 1

Opposite(c) == IF c \in CarsLeft THEN CarsRight ELSE CarsLeft

\* Position where a car enters the road.
EntryPos(c) == IF c \in CarsLeft THEN MinPos ELSE MaxPos

\* Position just before the bridge, where a car waits to enter it.
WaitPos(c)  == IF c \in CarsLeft THEN BridgeStart - 1 ELSE BridgeEnd + 1

\* Last bridge position before the car leaves the system.
LastPos(c)  == IF c \in CarsLeft THEN BridgeEnd ELSE BridgeStart

NextLoc(c) ==
    IF loc[c] = OffRoad THEN EntryPos(c)
    ELSE IF loc[c] = LastPos(c) THEN OffRoad
    ELSE IF c \in CarsLeft THEN loc[c] + 1
    ELSE loc[c] - 1

Free(p) == \A c \in Cars : loc[c] # p

OnBridge(S) == {c \in S : loc[c] \in Bridge}

IsElem(c, s) == \E i \in 1..Len(s) : s[i] = c

-----------------------------------------------------------------------------
Init == /\ loc = [c \in Cars |-> OffRoad]
        /\ waiting = <<>>

(***************************************************************************)
(* Car c advances one step along its path.                                 *)
(***************************************************************************)
Move(c) ==
    LET nxt == NextLoc(c) IN
    /\ (nxt # OffRoad) => Free(nxt)
    /\ IF loc[c] = WaitPos(c)
          THEN \* entering the bridge
               /\ waiting # <<>>
               /\ Head(waiting) = c
               /\ OnBridge(Opposite(c)) = {}
               /\ waiting' = Tail(waiting)
          ELSE IF nxt = WaitPos(c)
                  THEN waiting' = Append(waiting, c)   \* arriving at the bridge
                  ELSE UNCHANGED waiting
    /\ loc' = [loc EXCEPT ![c] = nxt]

Next == \E c \in Cars : Move(c)

Fairness == \A c \in Cars : SF_vars(Move(c))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)
TypeOK ==
    /\ loc \in [Cars -> Positions \cup {OffRoad}]
    /\ waiting \in Seq(Cars)

\* Two cars never occupy the same position on the road.
NoCollision ==
    \A c1, c2 \in Cars :
        (c1 # c2 /\ loc[c1] \in Positions) => loc[c1] # loc[c2]

\* Cars going opposite ways are never on the bridge at the same time.
NoHeadOn ==
    ~(\E l \in CarsLeft, r \in CarsRight : loc[l] \in Bridge /\ loc[r] \in Bridge)

\* If a car from one side is on the bridge, no car from the other side is.
DirectionalExclusivity ==
    /\ OnBridge(CarsLeft)  # {} => OnBridge(CarsRight) = {}
    /\ OnBridge(CarsRight) # {} => OnBridge(CarsLeft)  = {}

\* A car never enters the bridge while opposite traffic is on it.
SafeEntry ==
    [][\A c \in Cars :
          (loc[c] \notin Bridge /\ loc'[c] \in Bridge) =>
              OnBridge(Opposite(c)) = {}]_vars

\* Each waiting car appears in the queue exactly once, and every queued car
\* is at its waiting position.
QueueConsistent ==
    /\ \A i, j \in 1..Len(waiting) : (i # j) => waiting[i] # waiting[j]
    /\ \A c \in Cars : (loc[c] = WaitPos(c)) <=> IsElem(c, waiting)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)

\* A car waiting at the bridge eventually gets onto it (no starvation).
WaitingCarsEventuallyCross ==
    \A c \in Cars : (loc[c] = WaitPos(c)) ~> (loc[c] \in Bridge)

\* A car on the bridge eventually completes its crossing.
EventuallyCompleteCrossing ==
    \A c \in Cars : (loc[c] \in Bridge) ~> (loc[c] = OffRoad)

\* Every car crosses the bridge infinitely often.
Progress ==
    \A c \in Cars : []<>(loc[c] \in Bridge)

\* Both directions get to use the bridge again and again.
BothDirectionsServed ==
    /\ (CarsLeft  # {}) => []<>(OnBridge(CarsLeft)  # {})
    /\ (CarsRight # {}) => []<>(OnBridge(CarsRight) # {})

-----------------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ NoCollision /\ NoHeadOn
                   /\ DirectionalExclusivity /\ QueueConsistent)
THEOREM Spec => SafeEntry
THEOREM Spec => WaitingCarsEventuallyCross /\ EventuallyCompleteCrossing
                /\ Progress /\ BothDirectionsServed
=============================================================================