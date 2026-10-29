------------------------- MODULE SingleLaneBridge -------------------------
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
ASSUME Positions \subseteq Nat /\ Bridge \subseteq Positions /\ Bridge # {}
ASSUME StartPos < StartBridge /\ EndPos > EndBridge

Cars == CarsRight \cup CarsLeft

CarsInBridge == { c \in Cars : Location[c] \in Bridge }

CarsBeforeBridge ==
    { c \in CarsRight : Location[c] = EndBridge + 1 }
    \cup { c \in CarsLeft : Location[c] = StartBridge - 1 }

\* Cars traveling "right" start at EndPos and move toward smaller positions;
\* cars traveling "left" start at StartPos and move toward larger positions.
\* The road wraps around so cars keep circulating.
RMove(pos) == IF pos > StartPos THEN pos - 1 ELSE EndPos
LMove(pos) == IF pos < EndPos THEN pos + 1 ELSE StartPos

NextLocation(car) ==
    IF car \in CarsRight THEN RMove(Location[car]) ELSE LMove(Location[car])

IsInjectiveSeq(s) == \A i, j \in DOMAIN s : i # j => s[i] # s[j]

TypeOK ==
    /\ Location \in [Cars -> Positions]
    /\ WaitingBeforeBridge \in Seq(Cars)

-----------------------------------------------------------------------------

Init ==
    /\ Location = [c \in Cars |-> IF c \in CarsRight THEN EndPos ELSE StartPos]
    /\ WaitingBeforeBridge \in
         { s \in [1..Cardinality(CarsBeforeBridge) -> CarsBeforeBridge] :
              IsInjectiveSeq(s) }

ChangeLocation(car) ==
    /\ IF \/ car \in CarsRight /\ NextLocation(car) = EndBridge + 1
          \/ car \in CarsLeft  /\ NextLocation(car) = StartBridge - 1
       THEN WaitingBeforeBridge' = Append(WaitingBeforeBridge, car)
       ELSE UNCHANGED WaitingBeforeBridge
    /\ Location' = [Location EXCEPT ![car] = NextLocation(car)]

\* Moving on the road outside the bridge (including leaving the bridge)
MoveOutsideBridge(car) ==
    /\ NextLocation(car) \notin Bridge
    /\ ChangeLocation(car)

\* Moving forward on the bridge, only if the next position is free
MoveInsideBridge(car) ==
    /\ car \in CarsInBridge
    /\ NextLocation(car) \in Bridge
    /\ \A c \in Cars : Location[c] # NextLocation(car)
    /\ ChangeLocation(car)

HaveSameDirection(car) ==
    \/ car \in CarsRight /\ \A c \in CarsInBridge : c \in CarsRight
    \/ car \in CarsLeft  /\ \A c \in CarsInBridge : c \in CarsLeft

\* The car at the head of the waiting queue enters the bridge
EnterBridge ==
    /\ Len(WaitingBeforeBridge) # 0
    /\ LET car == Head(WaitingBeforeBridge) IN
         /\ car \notin CarsInBridge
         /\ \/ CarsInBridge = {}
            \/ HaveSameDirection(car)
         /\ \A c \in Cars : Location[c] # NextLocation(car)
         /\ Location' = [Location EXCEPT ![car] = NextLocation(car)]
         /\ WaitingBeforeBridge' = Tail(WaitingBeforeBridge)

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
\* Safety

CollisionFree ==
    \A a, b \in CarsInBridge : a # b => Location[a] # Location[b]

RespectBridgeCapacity ==
    Cardinality(CarsInBridge) <= Cardinality(Bridge)

NoOppositeDirectionsOnBridge ==
    ~ (\E a \in CarsInBridge, b \in CarsInBridge :
           a \in CarsRight /\ b \in CarsLeft)

Invariants ==
    /\ TypeOK
    /\ CollisionFree
    /\ RespectBridgeCapacity
    /\ NoOppositeDirectionsOnBridge

\* Liveness

CarsEventuallyExitBridge ==
    \A car \in Cars : (Location[car] \in Bridge) ~> (Location[car] \notin Bridge)

CarsEventuallyEnterBridge ==
    \A car \in Cars : []<>(Location[car] \in Bridge)

THEOREM Spec => []Invariants
THEOREM Spec => CarsEventuallyExitBridge /\ CarsEventuallyEnterBridge
=============================================================================