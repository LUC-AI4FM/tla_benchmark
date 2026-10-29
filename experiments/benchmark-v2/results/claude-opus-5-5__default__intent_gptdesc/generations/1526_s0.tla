---------------------------- MODULE SingleLaneBridge ----------------------------
(***************************************************************************)
(* Single-lane bridge crossing protocol.                                   *)
(*                                                                         *)
(* The road is a sequence of discrete positions 1..RoadLength.  The        *)
(* contiguous segment BridgeStart..BridgeEnd is a single-lane bridge.      *)
(* Off the bridge, the road has one lane per direction, so an eastbound    *)
(* and a westbound car may share an off-bridge position index.  On the     *)
(* bridge there is only one lane, so any two cars at the same bridge       *)
(* position collide.                                                       *)
(*                                                                         *)
(* Eastbound cars move 1 -> RoadLength.  Westbound cars move               *)
(* RoadLength -> 1.  Each car moves one position per step.  After passing  *)
(* the end of the road, a car returns on a return path to the start of its *)
(* own lane: east wraps RoadLength -> 1 and west wraps 1 -> RoadLength.    *)
(* It then tries to cross again.  This makes every car a car that          *)
(* "repeatedly attempts to cross".                                         *)
(*                                                                         *)
(* Bridge access protocol:                                                 *)
(*   - A car may enter the bridge only from its direction's entry position *)
(*     (the position just before the bridge).                              *)
(*   - A car may enter only when no opposite-direction car is on the       *)
(*     bridge and it is its direction's turn.                              *)
(*   - At most MaxBatch cars may enter per turn.                           *)
(*   - The turn passes to the other side when cars are waiting there and   *)
(*     either the batch is used up or nobody waits on the current side.    *)
(*     This prevents starvation.                                           *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS
    EastCars,      \* set of car identifiers travelling eastward
    WestCars,      \* set of car identifiers travelling westward
    RoadLength,    \* number of discrete road positions
    BridgeStart,   \* first position of the bridge
    BridgeEnd,     \* last position of the bridge
    MaxBatch       \* max number of entries per direction per turn

Cars      == EastCars \cup WestCars
Positions == 1..RoadLength
Bridge    == BridgeStart..BridgeEnd
Dirs      == {"E", "W"}

ASSUME ParamsOK ==
    /\ IsFiniteSet(EastCars) /\ IsFiniteSet(WestCars)
    /\ EastCars \cap WestCars = {}
    /\ RoadLength \in Nat /\ RoadLength >= 3
    /\ BridgeStart \in 2..(RoadLength - 1)
    /\ BridgeEnd \in BridgeStart..(RoadLength - 1)
    /\ MaxBatch \in Nat /\ MaxBatch >= 1
    \* Each lane has enough off-bridge room for its cars and always at least
    \* one free slot.
    /\ Cardinality(EastCars) <= RoadLength - Cardinality(Bridge)
    /\ Cardinality(WestCars) <= RoadLength - Cardinality(Bridge)

VARIABLES
    pos,     \* pos[c] : current position of car c
    turn,    \* direction currently allowed to enter the bridge
    passes   \* number of cars that entered during the current turn

vars == <<pos, turn, passes>>

-----------------------------------------------------------------------------
(* Helper operators *)

Dir(c)     == IF c \in EastCars THEN "E" ELSE "W"
Other(d)   == IF d = "E" THEN "W" ELSE "E"
CarsOf(d)  == IF d = "E" THEN EastCars ELSE WestCars

\* Next position of car c along its lane, including wrap-around return.
Succ(c) ==
    IF Dir(c) = "E"
    THEN IF pos[c] = RoadLength THEN 1 ELSE pos[c] + 1
    ELSE IF pos[c] = 1 THEN RoadLength ELSE pos[c] - 1

\* Position just before the bridge for each direction.
Entry(d) == IF d = "E" THEN BridgeStart - 1 ELSE BridgeEnd + 1

OnBridge(c) == pos[c] \in Bridge

NearSide(c) == IF Dir(c) = "E" THEN pos[c] < BridgeStart ELSE pos[c] > BridgeEnd
FarSide(c)  == IF Dir(c) = "E" THEN pos[c] > BridgeEnd   ELSE pos[c] < BridgeStart

AtEntry(c) == pos[c] = Entry(Dir(c))

\* Some car of direction d is waiting at the bridge entrance.
Waiting(d) == \E c \in CarsOf(d) : pos[c] = Entry(d)

\* Some car of the direction opposite to d is on the bridge.
OppositeOnBridge(d) == \E x \in CarsOf(Other(d)) : pos[x] \in Bridge

\* Position p is free for a car travelling in direction d.
Free(p, d) ==
    IF p \in Bridge
    THEN \A x \in Cars : pos[x] # p          \* single shared lane
    ELSE \A x \in CarsOf(d) : pos[x] # p     \* per-direction lane

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ pos \in [Cars -> Positions \ Bridge]
    /\ \A c, d \in Cars : (c # d /\ Dir(c) = Dir(d)) => pos[c] # pos[d]
    /\ turn \in Dirs
    /\ passes = 0

-----------------------------------------------------------------------------
(* Actions *)

\* Car c, waiting at its entry position, enters the bridge.
Enter(c) ==
    /\ AtEntry(c)
    /\ turn = Dir(c)
    /\ passes < MaxBatch
    /\ ~OppositeOnBridge(Dir(c))
    /\ Free(Succ(c), Dir(c))
    /\ pos' = [pos EXCEPT ![c] = Succ(c)]
    /\ passes' = passes + 1
    /\ UNCHANGED turn

\* Car c moves forward one position: on the approach, on the bridge,
\* off the bridge, or wrapping back to the start of its lane.
Drive(c) ==
    /\ ~AtEntry(c)
    /\ Free(Succ(c), Dir(c))
    /\ pos' = [pos EXCEPT ![c] = Succ(c)]
    /\ UNCHANGED <<turn, passes>>

\* A single scheduling attempt by car c.
CarStep(c) == Enter(c) \/ Drive(c)

\* Hand the bridge over to the other side.
SwitchTurn ==
    /\ Waiting(Other(turn))
    /\ (passes = MaxBatch \/ ~Waiting(turn))
    /\ turn' = Other(turn)
    /\ passes' = 0
    /\ UNCHANGED pos

\* Batch used up but nobody waits on the other side: start a new batch.
ResetBatch ==
    /\ passes = MaxBatch
    /\ ~Waiting(Other(turn))
    /\ passes' = 0
    /\ UNCHANGED <<pos, turn>>

\* Nondeterministic scheduling of car move attempts and controller actions.
Next ==
    \/ \E c \in Cars : CarStep(c)
    \/ SwitchTurn
    \/ ResetBatch

Fairness ==
    /\ \A c \in Cars : SF_vars(CarStep(c))
    /\ WF_vars(SwitchTurn)
    /\ WF_vars(ResetBatch)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety invariants *)

TypeOK ==
    /\ pos \in [Cars -> Positions]
    /\ turn \in Dirs
    /\ passes \in 0..MaxBatch

\* Collision detection: no head-on collisions.
\* Never are an eastbound and a westbound car on the bridge together.
NoHeadOnCollision ==
    ~(\E e \in EastCars, w \in WestCars : OnBridge(e) /\ OnBridge(w))

\* At most one direction occupies the bridge at any time.
BridgeOneDirection ==
    \A c, d \in Cars : (OnBridge(c) /\ OnBridge(d)) => Dir(c) = Dir(d)

\* Position-conflict detection.
\* Two distinct cars may share a position index only if they are in
\* different off-bridge lanes.  No two cars may share a bridge position.
NoPositionConflict ==
    \A c, d \in Cars :
        (c # d /\ pos[c] = pos[d]) => (Dir(c) # Dir(d) /\ pos[c] \notin Bridge)

NoBridgeSharing ==
    \A c, d \in Cars : (c # d /\ OnBridge(c) /\ OnBridge(d)) => pos[c] # pos[d]

NoCollision == NoHeadOnCollision /\ NoPositionConflict /\ NoBridgeSharing

\* Deadlock detection: the system can always take a step.
NoDeadlock == ENABLED Next

\* No mutual blocking: if cars are waiting on both sides, some car can
\* still move or the controller can hand over the bridge.
NoMutualBlocking ==
    (Waiting("E") /\ Waiting("W")) =>
        \/ \E c \in Cars : ENABLED CarStep(c)
        \/ ENABLED SwitchTurn

SafetyInvariant ==
    /\ TypeOK
    /\ NoCollision
    /\ BridgeOneDirection
    /\ NoDeadlock
    /\ NoMutualBlocking

-----------------------------------------------------------------------------
(* Ordering: no overtaking among cars of the same direction *)

Peers(c) == CarsOf(Dir(c)) \ {c}

\* Forward distance (along the lane cycle) from car c to car d.
Dist(c, d) ==
    IF Dir(c) = "E"
    THEN (pos[d] - pos[c]) % RoadLength
    ELSE (pos[c] - pos[d]) % RoadLength

\* The car immediately ahead of c in its lane.
CarAhead(c) ==
    CHOOSE d \in Peers(c) : \A e \in Peers(c) : Dist(c, d) <= Dist(c, e)

\* Same-direction ordering is preserved by every step.
NoOvertaking ==
    [][\A c \in Cars : Peers(c) # {} => CarAhead(c)' = CarAhead(c)]_vars

\* Each step moves at most one car, and only by one position along its lane.
SingleStepMoves ==
    [][\A c \in Cars : pos'[c] # pos[c] =>
            /\ pos'[c] = Succ(c)
            /\ \A d \in Cars \ {c} : pos'[d] = pos[d]]_vars

\* A car enters the bridge only from its entry position.
EnterOnlyFromEntry ==
    [][\A c \in Cars : (~OnBridge(c) /\ pos'[c] \in Bridge) => AtEntry(c)]_vars

-----------------------------------------------------------------------------
(* Liveness properties *)

\* No starvation: every car on the near side eventually reaches the far side.
StarvationFree ==
    \A c \in Cars : NearSide(c) ~> FarSide(c)

\* Every car waiting at the bridge entrance eventually gets onto the bridge.
WaitingEventuallyEnters ==
    \A c \in Cars : AtEntry(c) ~> OnBridge(c)

\* Cars that repeatedly attempt to cross visit the bridge infinitely often.
InfinitelyOftenOnBridge ==
    \A c \in Cars : []<>OnBridge(c)

\* Each car makes progress infinitely often (no permanent blocking).
NoPermanentBlocking ==
    \A c \in Cars : []<><<CarStep(c)>>_vars

LivenessProperty ==
    /\ StarvationFree
    /\ WaitingEventuallyEnters
    /\ InfinitelyOftenOnBridge
    /\ NoPermanentBlocking

-----------------------------------------------------------------------------
(* Assertions to check *)

THEOREM Spec => []SafetyInvariant
THEOREM Spec => NoOvertaking /\ SingleStepMoves /\ EnterOnlyFromEntry
THEOREM Spec => LivenessProperty

=============================================================================