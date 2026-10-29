------------------------------ MODULE SingleLaneBridge ------------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS CarsRight, CarsLeft, Bridge, Positions

VARIABLES Location, WaitingBeforeBridge

vars == <<Location, WaitingBeforeBridge>>

-----------------------------------------------------------------------------
StartPos    == CHOOSE min \in Positions : \A p \in Positions : min <= p
EndPos      == CHOOSE max \in Positions : \A p \in Positions : max >= p
StartBridge == CHOOSE min \in Bridge : \A e \in Bridge : min <= e
EndBridge   == CHOOSE max \in Bridge : \A e \in Bridge : max >= e

ASSUME CarsRight \cap CarsLeft = {}
ASSUME Positions \subseteq Nat /\ Positions # {}
ASSUME Bridge \subseteq Positions /\ Bridge # {}
ASSUME Positions = StartPos..EndPos
ASSUME Bridge = StartBridge..EndBridge
ASSUME StartPos < StartBridge - 1 /\ EndBridge + 1 < EndPos

Cars == CarsRight \cup CarsLeft

CarsInBridge == { c \in Cars : Location[c] \in Bridge }

\* Cars in CarsRight travel toward decreasing positions, CarsLeft toward increasing
RMove(pos) == IF pos > StartPos THEN pos - 1 ELSE EndPos
LMove(pos) == IF pos < EndPos THEN pos + 1 ELSE StartPos

NextLocation(car) ==
    IF car \in CarsRight THEN RMove(Location[car]) ELSE LMove(Location[car])

\* Position immediately before the bridge, in the direction of travel
BeforeBridge(car) ==
    IF car \in CarsRight THEN EndBridge + 1 ELSE StartBridge - 1

HaveSameDirection(c1, c2) ==
    \/ c1 \in CarsRight /\ c2 \in CarsRight
    \/ c1 \in CarsLeft  /\ c2 \in CarsLeft

-----------------------------------------------------------------------------
\* Movement of a car outside the bridge; reaching the waiting spot enqueues it
MoveOutsideBridge(car) ==
    /\ Location[car] \notin Bridge
    /\ Location[car] # BeforeBridge(car)
    /\ Location' = [Location EXCEPT ![car] = NextLocation(car)]
    /\ IF NextLocation(car) = BeforeBridge(car)
         THEN WaitingBeforeBridge' = Append(WaitingBeforeBridge, car)
         ELSE UNCHANGED WaitingBeforeBridge

\* Movement of a car already on the bridge (forward, or exiting it)
MoveInsideBridge(car) ==
    /\ car \in CarsInBridge
    /\ \A d \in CarsInBridge \ {car} : Location[d] # NextLocation(car)
    /\ Location' = [Location EXCEPT ![car] = NextLocation(car)]
    /\ UNCHANGED WaitingBeforeBridge

\* The first waiting car enters the bridge if no opposite traffic is on it
EnterBridge ==
    /\ WaitingBeforeBridge # <<>>
    /\ LET car == Head(WaitingBeforeBridge) IN
         /\ \A d \in CarsInBridge : HaveSameDirection(car, d)
         /\ \A d \in CarsInBridge : Location[d] # NextLocation(car)
         /\ Location' = [Location EXCEPT ![car] = NextLocation(car)]
         /\ WaitingBeforeBridge' = Tail(WaitingBeforeBridge)

-----------------------------------------------------------------------------
Init ==
    /\ Location = [c \in Cars |-> IF c \in CarsRight THEN EndPos ELSE StartPos]
    /\ WaitingBeforeBridge = <<>>

Next ==
    \/ \E car \in Cars : MoveOutsideBridge(car)
    \/ \E car \in Cars : MoveInsideBridge(car)
    \/ EnterBridge

Fairness ==
    /\ \A car \in Cars : WF_vars(MoveOutsideBridge(car))
    /\ \A car \in Cars : WF_vars(MoveInsideBridge(car))
    /\ WF_vars(EnterBridge)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Typing
TypeOK ==
    /\ Location \in [Cars -> Positions]
    /\ WaitingBeforeBridge \in Seq(Cars)
    /\ \A i, j \in 1..Len(WaitingBeforeBridge) :
          i # j => WaitingBeforeBridge[i] # WaitingBeforeBridge[j]

\* Safety: no cars of opposite directions on the bridge at the same time
NoOppositeCarsOnBridge ==
    \A c1, c2 \in CarsInBridge : HaveSameDirection(c1, c2)

\* Safety: no two cars occupy the same bridge position (no collisions)
NoCollisions ==
    \A c1, c2 \in CarsInBridge : c1 # c2 => Location[c1] # Location[c2]

Invariants == TypeOK /\ NoOppositeCarsOnBridge /\ NoCollisions

\* Liveness: every car eventually enters the bridge
EventuallyEnterBridge ==
    \A car \in Cars : []<>(Location[car] \in Bridge)

\* Liveness: every car on the bridge eventually exits it
EventuallyExitBridge ==
    \A car \in Cars : (Location[car] \in Bridge) ~> (Location[car] \notin Bridge)

THEOREM Spec => []Invariants
THEOREM Spec => EventuallyEnterBridge /\ EventuallyExitBridge
=============================================================================