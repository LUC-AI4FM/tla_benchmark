---------------------------- MODULE SingleLaneBridge ----------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS CarsRight, CarsLeft, Bridge, Positions

VARIABLES Location, WaitingBeforeBridge

vars == <<Location, WaitingBeforeBridge>>

Cars == CarsRight \cup CarsLeft

StartPos    == CHOOSE min \in Positions : \A p \in Positions : min <= p
EndPos      == CHOOSE max \in Positions : \A p \in Positions : max >= p
StartBridge == CHOOSE min \in Bridge : \A e \in Bridge : min <= e
EndBridge   == CHOOSE max \in Bridge : \A e \in Bridge : max >= e

ASSUME CarsRight \cap CarsLeft = {}
ASSUME Cardinality(CarsRight \cup CarsLeft) # 0
ASSUME Positions \subseteq Nat /\ Positions # {}
ASSUME Bridge \subseteq Positions /\ Bridge # {}
ASSUME Positions = StartPos..EndPos
ASSUME Bridge = StartBridge..EndBridge
ASSUME StartPos < StartBridge - 1 /\ EndBridge + 1 < EndPos

\* Cars in CarsRight travel from right to left (decreasing positions),
\* cars in CarsLeft travel from left to right (increasing positions).
\* The road outside the bridge is a circuit, so cars come back around.
RMove(pos) == IF pos > StartPos THEN pos - 1 ELSE EndPos
LMove(pos) == IF pos < EndPos   THEN pos + 1 ELSE StartPos

NextLocation(car) ==
    IF car \in CarsRight THEN RMove(Location[car]) ELSE LMove(Location[car])

\* Position just before the bridge where a car waits to enter
WaitPos(car) == IF car \in CarsRight THEN EndBridge + 1 ELSE StartBridge - 1

CarsOnBridge == { c \in Cars : Location[c] \in Bridge }

SameDirection(c1, c2) == (c1 \in CarsRight) <=> (c2 \in CarsRight)

Occupied(pos, car) == \E c \in Cars \ {car} : Location[c] = pos

-----------------------------------------------------------------------------

TypeOK ==
    /\ Location \in [Cars -> Positions]
    /\ WaitingBeforeBridge \in Seq(Cars)

Init ==
    /\ Location \in [Cars -> Positions \ (Bridge \cup {StartBridge - 1, EndBridge + 1})]
    /\ WaitingBeforeBridge = <<>>

\* Ordinary movement of a car (outside the bridge, along the bridge, or leaving it).
\* A car waiting before the bridge cannot move until it is allowed to enter.
Move(car) ==
    /\ Location[car] # WaitPos(car)
    /\ LET nxt == NextLocation(car) IN
         /\ nxt \in Bridge => ~Occupied(nxt, car)
         /\ Location' = [Location EXCEPT ![car] = nxt]
         /\ IF nxt = WaitPos(car)
              THEN WaitingBeforeBridge' = Append(WaitingBeforeBridge, car)
              ELSE UNCHANGED WaitingBeforeBridge

\* The first waiting car enters the bridge if no car of the opposite
\* direction is on it and the entry position is free.
Enter(car) ==
    /\ WaitingBeforeBridge # <<>>
    /\ Head(WaitingBeforeBridge) = car
    /\ Location[car] = WaitPos(car)
    /\ \A c \in CarsOnBridge : SameDirection(c, car)
    /\ ~Occupied(NextLocation(car), car)
    /\ Location' = [Location EXCEPT ![car] = NextLocation(car)]
    /\ WaitingBeforeBridge' = Tail(WaitingBeforeBridge)

Next == \E car \in Cars : Move(car) \/ Enter(car)

Fairness ==
    \A car \in Cars : WF_vars(Move(car)) /\ WF_vars(Enter(car))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety

\* Cars going in opposite directions are never on the bridge simultaneously
NoOppositeOnBridge ==
    ~(\E r \in CarsRight, l \in CarsLeft :
         Location[r] \in Bridge /\ Location[l] \in Bridge)

\* No two cars share a position on the bridge
NoCollision ==
    \A c1, c2 \in Cars :
        (c1 # c2 /\ Location[c1] \in Bridge) => Location[c1] # Location[c2]

\* Waiting queue holds distinct cars that are indeed waiting before the bridge
QueueOK ==
    /\ \A i, j \in 1..Len(WaitingBeforeBridge) :
          i # j => WaitingBeforeBridge[i] # WaitingBeforeBridge[j]
    /\ \A i \in 1..Len(WaitingBeforeBridge) :
          Location[WaitingBeforeBridge[i]] = WaitPos(WaitingBeforeBridge[i])

Safety == NoOppositeOnBridge /\ NoCollision

Inv == TypeOK /\ Safety /\ QueueOK

THEOREM Spec => [](TypeOK /\ Safety /\ QueueOK)

-----------------------------------------------------------------------------
\* Liveness

EventuallyEnter ==
    \A car \in Cars : (Location[car] \notin Bridge) ~> (Location[car] \in Bridge)

EventuallyExit ==
    \A car \in Cars : (Location[car] \in Bridge) ~> (Location[car] \notin Bridge)

Liveness == EventuallyEnter /\ EventuallyExit

THEOREM Spec => Liveness

=============================================================================