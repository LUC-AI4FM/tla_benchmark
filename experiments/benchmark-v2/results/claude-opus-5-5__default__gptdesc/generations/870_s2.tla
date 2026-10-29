------------------------- MODULE SingleLaneBridge -------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS CarsRight, CarsLeft, Bridge, Positions

VARIABLES Location, WaitingBeforeBridge

vars == <<Location, WaitingBeforeBridge>>

StartPos    == CHOOSE min \in Positions : \A p \in Positions : min <= p
EndPos      == CHOOSE max \in Positions : \A p \in Positions : max >= p
StartBridge == CHOOSE min \in Bridge : \A e \in Bridge : min <= e
EndBridge   == CHOOSE max \in Bridge : \A e \in Bridge : max >= e

ASSUME Positions \subseteq Nat
ASSUME Bridge \subseteq Positions
ASSUME CarsRight \cap CarsLeft = {}
ASSUME Cardinality(CarsRight \union CarsLeft) # 0
ASSUME StartPos < StartBridge /\ EndBridge < EndPos

Cars == CarsRight \union CarsLeft

CarsInBridge == { c \in Cars : Location[c] \in Bridge }

\* Cars in CarsRight travel towards decreasing positions, cars in CarsLeft
\* travel towards increasing positions; both wrap around at the ends.
RMove(pos) == IF pos > StartPos THEN pos - 1 ELSE EndPos
LMove(pos) == IF pos < EndPos THEN pos + 1 ELSE StartPos

NextLocation(car) ==
    IF car \in CarsRight THEN RMove(Location[car]) ELSE LMove(Location[car])

\* Moving a car; if it arrives just before the bridge it starts waiting.
ChangeLocation(car) ==
    /\ IF \/ car \in CarsRight /\ NextLocation(car) = EndBridge + 1
          \/ car \in CarsLeft  /\ NextLocation(car) = StartBridge - 1
       THEN WaitingBeforeBridge' = Append(WaitingBeforeBridge, car)
       ELSE UNCHANGED WaitingBeforeBridge
    /\ Location' = [Location EXCEPT ![car] = NextLocation(car)]

HaveSameDirection(car) ==
    \/ car \in CarsRight /\ \A c \in CarsInBridge : c \in CarsRight
    \/ car \in CarsLeft  /\ \A c \in CarsInBridge : c \in CarsLeft

\* A car moves outside of the bridge (never into it).
MoveOutsideBridge(car) ==
    /\ Location[car] \notin Bridge
    /\ NextLocation(car) \notin Bridge
    /\ ChangeLocation(car)

\* A car on the bridge moves forward (or leaves it) without colliding.
MoveInsideBridge(car) ==
    /\ car \in CarsInBridge
    /\ \A c \in Cars : Location[c] # NextLocation(car)
    /\ ChangeLocation(car)

\* The first waiting car enters the bridge if allowed.
EnterBridge ==
    /\ Len(WaitingBeforeBridge) # 0
    /\ LET car == Head(WaitingBeforeBridge) IN
         /\ car \notin CarsInBridge
         /\ HaveSameDirection(car)
         /\ \A c \in Cars : Location[c] # NextLocation(car)
         /\ Location' = [Location EXCEPT ![car] = NextLocation(car)]
         /\ WaitingBeforeBridge' = Tail(WaitingBeforeBridge)

Init ==
    /\ Location = [c \in Cars |-> IF c \in CarsRight THEN EndPos ELSE StartPos]
    /\ WaitingBeforeBridge = <<>>

Next ==
    \/ EnterBridge
    \/ \E car \in Cars : MoveOutsideBridge(car) \/ MoveInsideBridge(car)

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
    /\ Len(WaitingBeforeBridge) <= Cardinality(Cars)

\* Safety: no opposite directions on the bridge at the same time
NoOppositeDirectionsOnBridge ==
    \/ CarsInBridge \subseteq CarsRight
    \/ CarsInBridge \subseteq CarsLeft

\* Safety: no two cars occupy the same bridge position
NoCollisionOnBridge ==
    \A a, b \in CarsInBridge : a # b => Location[a] # Location[b]

Invariants ==
    /\ TypeOK
    /\ NoOppositeDirectionsOnBridge
    /\ NoCollisionOnBridge

-----------------------------------------------------------------------------
\* Liveness
CarsEnterBridge == \A car \in Cars : <>(Location[car] \in Bridge)

CarsLeaveBridge == \A car \in Cars : <>(Location[car] \notin Bridge)

THEOREM Spec => []Invariants
THEOREM Spec => CarsEnterBridge /\ CarsLeaveBridge
=============================================================================