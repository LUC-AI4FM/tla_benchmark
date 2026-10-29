---------------------------- MODULE MC ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CarsRight, CarsLeft, Bridge, Positions

VARIABLES Location, WaitingBeforeBridge

vars == <<Location, WaitingBeforeBridge>>

\* Constant definitions used by the model-checking configuration
const_1615720459299211000 == {"r1", "r2"}
const_1615720459299212000 == {"l1", "l2"}
const_1615720459299213000 == {4, 5}
const_1615720459299214000 == 1..8

Cars == CarsRight \cup CarsLeft

MaxOf(S) == CHOOSE x \in S : \A y \in S : y <= x
MinOf(S) == CHOOSE x \in S : \A y \in S : x <= y

\* Cars from the right travel toward decreasing positions,
\* cars from the left travel toward increasing positions.
StartPos(c) == IF c \in CarsRight THEN MaxOf(Positions) ELSE MinOf(Positions)

BeforeBridge(c) == IF c \in CarsRight THEN MaxOf(Bridge) + 1 ELSE MinOf(Bridge) - 1

NextPos(c) ==
    IF c \in CarsRight
    THEN IF Location[c] = MinOf(Positions) THEN MaxOf(Positions) ELSE Location[c] - 1
    ELSE IF Location[c] = MaxOf(Positions) THEN MinOf(Positions) ELSE Location[c] + 1

SameDirection(c) == IF c \in CarsRight THEN CarsRight ELSE CarsLeft
OppositeDirection(c) == IF c \in CarsRight THEN CarsLeft ELSE CarsRight

CarsOnBridge == {c \in Cars : Location[c] \in Bridge}

Init ==
    /\ Location = [c \in Cars |-> StartPos(c)]
    /\ WaitingBeforeBridge = <<>>

\* Move along the road outside the bridge
MoveOutside(c) ==
    /\ Location[c] \notin Bridge
    /\ Location[c] /= BeforeBridge(c)
    /\ Location' = [Location EXCEPT ![c] = NextPos(c)]
    /\ WaitingBeforeBridge' =
          IF NextPos(c) = BeforeBridge(c)
          THEN Append(WaitingBeforeBridge, c)
          ELSE WaitingBeforeBridge

\* Enter the bridge: must be first in line and no oncoming car on the bridge
EnterBridge(c) ==
    /\ Location[c] = BeforeBridge(c)
    /\ WaitingBeforeBridge /= <<>>
    /\ Head(WaitingBeforeBridge) = c
    /\ \A o \in OppositeDirection(c) : Location[o] \notin Bridge
    /\ Location' = [Location EXCEPT ![c] = NextPos(c)]
    /\ WaitingBeforeBridge' = Tail(WaitingBeforeBridge)

\* Move within or leave the bridge
MoveOnBridge(c) ==
    /\ Location[c] \in Bridge
    /\ Location' = [Location EXCEPT ![c] = NextPos(c)]
    /\ UNCHANGED WaitingBeforeBridge

CarNext(c) == MoveOutside(c) \/ EnterBridge(c) \/ MoveOnBridge(c)

Next == \E c \in Cars : CarNext(c)

Fairness == \A c \in Cars : WF_vars(CarNext(c))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------

TypeOK ==
    /\ Location \in [Cars -> Positions]
    /\ WaitingBeforeBridge \in Seq(Cars)

NoCollision ==
    ~ \E r \in CarsRight, l \in CarsLeft :
        Location[r] \in Bridge /\ Location[l] \in Bridge

QueueNoDuplicates ==
    \A i, j \in 1..Len(WaitingBeforeBridge) :
        i /= j => WaitingBeforeBridge[i] /= WaitingBeforeBridge[j]

Invariants == TypeOK /\ NoCollision /\ QueueNoDuplicates

CarsInBridgeExitBridge ==
    \A c \in Cars : (Location[c] \in Bridge) ~> (Location[c] \notin Bridge)

CarsEnterBridge ==
    \A c \in Cars : (Location[c] = BeforeBridge(c)) ~> (Location[c] \in Bridge)

CarsInfOftenOnBridge ==
    \A c \in CarsRight : []<>(Location[c] \in Bridge)

=============================================================================