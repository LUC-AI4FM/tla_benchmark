------------------------------ MODULE SingleLaneBridge ------------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS CarsRight, CarsLeft, Bridge, Positions

VARIABLES Location, WaitingBeforeBridge

vars == <<Location, WaitingBeforeBridge>>

Min(S) == CHOOSE m \in S : \A x \in S : m <= x
Max(S) == CHOOSE m \in S : \A x \in S : m >= x

StartPos    == Min(Positions)
EndPos      == Max(Positions)
StartBridge == Min(Bridge)
EndBridge   == Max(Bridge)

ASSUME CarsRight \cap CarsLeft = {}
ASSUME Cardinality(CarsRight \cup CarsLeft) # 0
ASSUME Positions \subseteq Nat /\ Positions # {}
ASSUME Bridge \subseteq Positions /\ Bridge # {}
ASSUME Positions = StartPos..EndPos
ASSUME Bridge = StartBridge..EndBridge
ASSUME StartPos + 1 < StartBridge /\ EndBridge + 1 < EndPos

Cars == CarsRight \cup CarsLeft

(* Cars traveling right move toward decreasing positions, left cars toward increasing *)
RMove(pos) == IF pos > StartPos THEN pos - 1 ELSE EndPos
LMove(pos) == IF pos < EndPos THEN pos + 1 ELSE StartPos

NextLocation(car) ==
    IF car \in CarsRight THEN RMove(Location[car]) ELSE LMove(Location[car])

(* Position just before the bridge, depending on direction *)
WaitingPos(car) == IF car \in CarsRight THEN EndBridge + 1 ELSE StartBridge - 1

CarsInBridge == { c \in Cars : Location[c] \in Bridge }

HaveSameDirection(c1, c2) ==
    \/ c1 \in CarsRight /\ c2 \in CarsRight
    \/ c1 \in CarsLeft  /\ c2 \in CarsLeft

ChangeLocation(car) ==
    /\ Location' = [Location EXCEPT ![car] = NextLocation(car)]
    /\ IF NextLocation(car) = WaitingPos(car)
          THEN WaitingBeforeBridge' = Append(WaitingBeforeBridge, car)
          ELSE UNCHANGED WaitingBeforeBridge

(* Movement of a car outside the bridge (cannot move into the bridge this way) *)
MoveOutsideBridge(car) ==
    /\ Location[car] \notin Bridge
    /\ NextLocation(car) \notin Bridge
    /\ ChangeLocation(car)

(* Movement of a car on the bridge: no collision with a car ahead on the bridge *)
MoveInsideBridge(car) ==
    /\ Location[car] \in Bridge
    /\ NextLocation(car) \in Bridge =>
           \A c \in Cars \ {car} : Location[c] # NextLocation(car)
    /\ ChangeLocation(car)

(* The first waiting car enters the bridge *)
EnterBridge ==
    /\ Len(WaitingBeforeBridge) # 0
    /\ LET car == Head(WaitingBeforeBridge) IN
         /\ NextLocation(car) \in Bridge
         /\ \A c \in CarsInBridge : HaveSameDirection(car, c)
         /\ \A c \in Cars \ {car} : Location[c] # NextLocation(car)
         /\ Location' = [Location EXCEPT ![car] = NextLocation(car)]
         /\ WaitingBeforeBridge' = Tail(WaitingBeforeBridge)

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
(* Invariants *)

TypeOK ==
    /\ Location \in [Cars -> Positions]
    /\ WaitingBeforeBridge \in Seq(Cars)
    /\ Len(WaitingBeforeBridge) <= Cardinality(Cars)

(* Cars traveling in opposite directions are never on the bridge together *)
NoOppositeDirectionsOnBridge ==
    ~ \E r \in CarsRight, l \in CarsLeft :
        /\ Location[r] \in Bridge
        /\ Location[l] \in Bridge

(* No two cars occupy the same bridge position *)
NoCollision ==
    \A c1, c2 \in CarsInBridge : c1 # c2 => Location[c1] # Location[c2]

Invariants ==
    /\ TypeOK
    /\ NoOppositeDirectionsOnBridge
    /\ NoCollision

-----------------------------------------------------------------------------
(* Liveness *)

(* Every car eventually enters the bridge (infinitely often) *)
CarsEventuallyEnter ==
    \A car \in Cars : []<>(Location[car] \in Bridge)

(* Every car on the bridge eventually leaves it *)
CarsEventuallyExit ==
    \A car \in Cars : (Location[car] \in Bridge) ~> (Location[car] \notin Bridge)

THEOREM Spec => []Invariants
THEOREM Spec => CarsEventuallyEnter /\ CarsEventuallyExit
=============================================================================