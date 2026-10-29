------------------------------ MODULE SingleLaneBridge ------------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS CarsRight, CarsLeft, Bridge, Positions

VARIABLES Location, WaitingBeforeBridge

vars == <<Location, WaitingBeforeBridge>>

Cars == CarsRight \union CarsLeft

StartPos    == CHOOSE min \in Positions : \A p \in Positions : min <= p
EndPos      == CHOOSE max \in Positions : \A p \in Positions : max >= p
StartBridge == CHOOSE min \in Bridge : \A e \in Bridge : min <= e
EndBridge   == CHOOSE max \in Bridge : \A e \in Bridge : max >= e

ASSUME CarsRight \cap CarsLeft = {}
ASSUME Cardinality(Cars) # 0
ASSUME Bridge \subseteq Positions
ASSUME StartPos < StartBridge /\ EndPos > EndBridge
ASSUME Cardinality(Bridge) < Cardinality(Positions)

SetToSeq(S) ==
    CHOOSE f \in [1..Cardinality(S) -> S] :
        \A i, j \in 1..Cardinality(S) : f[i] = f[j] => i = j

\* Right-bound cars move from high positions to low positions,
\* left-bound cars move from low positions to high positions.
RMove(pos) == IF pos > StartPos THEN pos - 1 ELSE EndPos
LMove(pos) == IF pos < EndPos THEN pos + 1 ELSE StartPos

NextLocation(car) ==
    IF car \in CarsRight THEN RMove(Location[car]) ELSE LMove(Location[car])

CarsInBridge == { c \in Cars : Location[c] \in Bridge }

\* Position just before entering the bridge for each direction
WaitPos(car) == IF car \in CarsRight THEN EndBridge + 1 ELSE StartBridge - 1

IsWaitingPos(car, pos) == pos = WaitPos(car)

ChangeLocation(car) ==
    /\ IF IsWaitingPos(car, NextLocation(car))
         THEN WaitingBeforeBridge' = Append(WaitingBeforeBridge, car)
         ELSE UNCHANGED WaitingBeforeBridge
    /\ Location' = [Location EXCEPT ![car] = NextLocation(car)]

HaveSameDirection(car) ==
    \/ car \in CarsRight /\ \A c \in CarsInBridge : c \in CarsRight
    \/ car \in CarsLeft  /\ \A c \in CarsInBridge : c \in CarsLeft

-----------------------------------------------------------------------------
\* Actions

MoveOutsideBridge(car) ==
    /\ Location[car] \notin Bridge
    /\ NextLocation(car) \notin Bridge
    /\ ChangeLocation(car)

MoveInsideBridge(car) ==
    /\ car \in CarsInBridge
    /\ \A c \in CarsInBridge : Location[c] # NextLocation(car)
    /\ ChangeLocation(car)

EnterBridge ==
    /\ Len(WaitingBeforeBridge) # 0
    /\ LET car == Head(WaitingBeforeBridge) IN
         /\ car \notin CarsInBridge
         /\ NextLocation(car) \in Bridge
         /\ \/ CarsInBridge = {}
            \/ /\ HaveSameDirection(car)
               /\ \A c \in Cars : Location[c] # NextLocation(car)
         /\ Location' = [Location EXCEPT ![car] = NextLocation(car)]
         /\ WaitingBeforeBridge' = Tail(WaitingBeforeBridge)

Init ==
    /\ Location = [c \in Cars |-> IF c \in CarsRight THEN EndPos ELSE StartPos]
    /\ WaitingBeforeBridge =
         SetToSeq({ c \in Cars : IsWaitingPos(c, Location[c]) })

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
\* Invariants

TypeOK ==
    /\ Location \in [Cars -> Positions]
    /\ WaitingBeforeBridge \in Seq(Cars)

CollisionFree ==
    \A c1, c2 \in CarsInBridge : c1 # c2 => Location[c1] # Location[c2]

CapacityRespected == Cardinality(CarsInBridge) <= Cardinality(Bridge)

OneDirection ==
    ~ (\E cr \in CarsRight, cl \in CarsLeft :
          Location[cr] \in Bridge /\ Location[cl] \in Bridge)

Invariants ==
    /\ TypeOK
    /\ CollisionFree
    /\ CapacityRespected
    /\ OneDirection

-----------------------------------------------------------------------------
\* Liveness

CarsInBridgeExitBridge ==
    \A car \in Cars : (Location[car] \in Bridge) ~> (Location[car] \notin Bridge)

CarsEnterBridge ==
    \A car \in Cars : (Location[car] \notin Bridge) ~> (Location[car] \in Bridge)

=============================================================================