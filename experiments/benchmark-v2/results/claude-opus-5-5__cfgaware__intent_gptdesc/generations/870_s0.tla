------------------------- MODULE SingleLaneBridge -------------------------
(***************************************************************************)
(* A single-lane bridge crossed by cars from two opposite directions.     *)
(*                                                                         *)
(* Positions is an ordered, contiguous set of integers.  Bridge is a       *)
(* contiguous subset strictly inside Positions.  CarsRight move toward     *)
(* higher positions and CarsLeft move toward lower positions.  After       *)
(* leaving the far end of the road, a car wraps around to its starting     *)
(* end and approaches the bridge again, so behaviors are infinite.         *)
(*                                                                         *)
(* A car reaching the position just before the bridge joins a FIFO queue   *)
(* (WaitingBeforeBridge).  Only the head of the queue may enter.  It may   *)
(* enter only if every car already on the bridge moves in its direction    *)
(* and the entry position is free.  This prevents starvation.              *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS CarsRight, CarsLeft, Bridge, Positions

VARIABLES Location, WaitingBeforeBridge

vars == <<Location, WaitingBeforeBridge>>

Cars == CarsRight \cup CarsLeft

StartPos    == CHOOSE p \in Positions : \A q \in Positions : p <= q
EndPos      == CHOOSE p \in Positions : \A q \in Positions : p >= q
StartBridge == CHOOSE p \in Bridge : \A q \in Bridge : p <= q
EndBridge   == CHOOSE p \in Bridge : \A q \in Bridge : p >= q

(***************************************************************************)
(* Environment assumptions                                                 *)
(***************************************************************************)
ASSUME CarsRight \cap CarsLeft = {}
ASSUME Cars # {}
ASSUME Bridge # {}
ASSUME Positions \subseteq Int /\ Bridge \subseteq Positions
ASSUME Positions = StartPos..EndPos
ASSUME Bridge = StartBridge..EndBridge
ASSUME StartPos < StartBridge /\ EndBridge < EndPos

(***************************************************************************)
(* Helper definitions                                                      *)
(***************************************************************************)
Range(s) == { s[i] : i \in DOMAIN s }

\* Deterministic step-forward movement rule.
NextPos(c, pos) ==
    IF c \in CarsRight
    THEN IF pos = EndPos THEN StartPos ELSE pos + 1
    ELSE IF pos = StartPos THEN EndPos ELSE pos - 1

NextLocation(c) == NextPos(c, Location[c])

\* The approach position directly in front of the bridge for car c.
WaitPos(c) == IF c \in CarsRight THEN StartBridge - 1 ELSE EndBridge + 1

CarsInBridge == { c \in Cars : Location[c] \in Bridge }

SameDirection(c, d) ==
    \/ c \in CarsRight /\ d \in CarsRight
    \/ c \in CarsLeft  /\ d \in CarsLeft

PositionFree(p) == \A c \in Cars : Location[c] # p

(***************************************************************************)
(* Initial state: all cars off the bridge at the ends of the road.         *)
(***************************************************************************)
InitLocation == [c \in Cars |-> IF c \in CarsRight THEN StartPos ELSE EndPos]

InitWaiting == { c \in Cars : InitLocation[c] = WaitPos(c) }

InjectiveSeqs(S) ==
    { f \in [1..Cardinality(S) -> S] :
        \A i, j \in 1..Cardinality(S) : f[i] = f[j] => i = j }

Init ==
    /\ Location = InitLocation
    /\ WaitingBeforeBridge \in InjectiveSeqs(InitWaiting)

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

\* A car on the approach/exit lanes steps forward (not onto the bridge).
\* If it arrives at the position before the bridge, it joins the queue.
MoveOutsideBridge(c) ==
    /\ Location[c] \notin Bridge
    /\ c \notin Range(WaitingBeforeBridge)
    /\ NextLocation(c) \notin Bridge
    /\ Location' = [Location EXCEPT ![c] = NextLocation(c)]
    /\ IF NextLocation(c) = WaitPos(c)
       THEN WaitingBeforeBridge' = Append(WaitingBeforeBridge, c)
       ELSE UNCHANGED WaitingBeforeBridge

\* A car on the bridge steps forward along the bridge or exits it.
MoveInsideBridge(c) ==
    /\ Location[c] \in Bridge
    /\ NextLocation(c) \in Bridge => PositionFree(NextLocation(c))
    /\ Location' = [Location EXCEPT ![c] = NextLocation(c)]
    /\ UNCHANGED WaitingBeforeBridge

\* The head of the queue enters the bridge if allowed.
EnterBridge ==
    /\ Len(WaitingBeforeBridge) > 0
    /\ LET h == Head(WaitingBeforeBridge)
       IN  /\ NextLocation(h) \in Bridge
           /\ PositionFree(NextLocation(h))
           /\ \A d \in CarsInBridge : SameDirection(h, d)
           /\ Location' = [Location EXCEPT ![h] = NextLocation(h)]
           /\ WaitingBeforeBridge' = Tail(WaitingBeforeBridge)

Next ==
    \/ \E c \in Cars : MoveOutsideBridge(c)
    \/ \E c \in Cars : MoveInsideBridge(c)
    \/ EnterBridge

Fairness ==
    /\ \A c \in Cars : WF_vars(MoveOutsideBridge(c))
    /\ \A c \in Cars : WF_vars(MoveInsideBridge(c))
    /\ WF_vars(EnterBridge)

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Safety invariants                                                       *)
(***************************************************************************)
TypeOK ==
    /\ Location \in [Cars -> Positions]
    /\ WaitingBeforeBridge \in Seq(Cars)

\* Never two cars moving in opposite directions on the bridge.
NoOppositeCarsOnBridge ==
    \A c, d \in CarsInBridge : SameDirection(c, d)

\* Never two cars occupying the same bridge position.
NoCollisionOnBridge ==
    \A c, d \in CarsInBridge : c # d => Location[c] # Location[d]

\* Bridge capacity is never exceeded.
CapacityRespected ==
    Cardinality(CarsInBridge) <= Cardinality(Bridge)

\* The queue holds distinct cars, each waiting just before the bridge.
QueueConsistent ==
    /\ \A i, j \in DOMAIN WaitingBeforeBridge :
          WaitingBeforeBridge[i] = WaitingBeforeBridge[j] => i = j
    /\ \A c \in Cars :
          (c \in Range(WaitingBeforeBridge)) <=> (Location[c] = WaitPos(c))

Invariants ==
    /\ TypeOK
    /\ NoOppositeCarsOnBridge
    /\ NoCollisionOnBridge
    /\ CapacityRespected
    /\ QueueConsistent

(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)

\* Every car off the bridge eventually enters the bridge.
CarsEnterBridge ==
    \A c \in Cars : (Location[c] \notin Bridge) ~> (Location[c] \in Bridge)

\* Every car on the bridge eventually exits the bridge.
CarsInBridgeExitBridge ==
    \A c \in Cars : (Location[c] \in Bridge) ~> (Location[c] \notin Bridge)

=============================================================================