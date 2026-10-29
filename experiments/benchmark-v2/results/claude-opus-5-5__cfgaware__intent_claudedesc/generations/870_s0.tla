--------------------------- MODULE SingleLaneBridge ---------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS CarsRight, CarsLeft, Bridge, Positions

VARIABLES Location, WaitingBeforeBridge

vars == <<Location, WaitingBeforeBridge>>

StartPos    == CHOOSE min \in Positions : \A p \in Positions : min <= p
EndPos      == CHOOSE max \in Positions : \A p \in Positions : max >= p
StartBridge == CHOOSE min \in Bridge : \A e \in Bridge : min <= e
EndBridge   == CHOOSE max \in Bridge : \A e \in Bridge : max >= e

ASSUME CarsRight \cap CarsLeft = {}
ASSUME Cardinality(CarsRight \cup CarsLeft) # 0
ASSUME Bridge \subseteq Positions /\ StartPos < StartBridge /\ EndPos > EndBridge

Cars == CarsRight \cup CarsLeft

Starting == [c \in Cars |-> IF c \in CarsRight THEN StartPos ELSE EndPos]

CarsInBridge == {c \in Cars : Location[c] \in Bridge}

RMove(pos) == IF pos > StartPos THEN pos - 1 ELSE EndPos
LMove(pos) == IF pos < EndPos THEN pos + 1 ELSE StartPos

NextLocation(car) ==
    IF car \in CarsRight THEN RMove(Location[car]) ELSE LMove(Location[car])

ChangeLocation(car) ==
    /\ IF \/ car \in CarsRight /\ NextLocation(car) = EndBridge + 1
          \/ car \in CarsLeft  /\ NextLocation(car) = StartBridge - 1
       THEN WaitingBeforeBridge' = Append(WaitingBeforeBridge, car)
       ELSE UNCHANGED WaitingBeforeBridge
    /\ Location' = [Location EXCEPT ![car] = NextLocation(car)]

HaveSameDirection(car) ==
    \/ car \in CarsRight /\ \A c \in Cars : Location[c] \in Bridge => c \in CarsRight
    \/ car \in CarsLeft  /\ \A c \in Cars : Location[c] \in Bridge => c \in CarsLeft

MoveOutsideBridge(car) ==
    /\ NextLocation(car) \notin Bridge
    /\ ChangeLocation(car)

MoveInsideBridge(car) ==
    /\ car \in CarsInBridge
    /\ \A c \in Cars : Location[c] # NextLocation(car)
    /\ ChangeLocation(car)

EnterBridge ==
    /\ Len(WaitingBeforeBridge) # 0
    /\ LET car == Head(WaitingBeforeBridge) IN
         /\ car \notin CarsInBridge
         /\ \/ CarsInBridge = {}
            \/ HaveSameDirection(car)
         /\ \A c \in Cars : Location[c] # NextLocation(car)
         /\ Location' = [Location EXCEPT ![car] = NextLocation(car)]
         /\ WaitingBeforeBridge' = Tail(WaitingBeforeBridge)

Init ==
    /\ Location = Starting
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

TypeOK ==
    /\ Location \in [Cars -> Positions]
    /\ WaitingBeforeBridge \in Seq(Cars)

NoCollision ==
    \A a, b \in CarsInBridge : a # b => Location[a] # Location[b]

NoHeadOnConflict ==
    CarsInBridge \subseteq CarsRight \/ CarsInBridge \subseteq CarsLeft

CapacityLimit ==
    Cardinality(CarsInBridge) <= Cardinality(Bridge)

Invariants ==
    /\ TypeOK
    /\ NoCollision
    /\ NoHeadOnConflict
    /\ CapacityLimit

CarsInBridgeExitBridge ==
    \A car \in Cars : Location[car] \in Bridge ~> Location[car] \notin Bridge

CarsEnterBridge ==
    \A car \in Cars : Location[car] \notin Bridge ~> Location[car] \in Bridge

=============================================================================