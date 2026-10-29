---------------------------- MODULE SingleLaneBridge ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CarsRight, CarsLeft, Bridge, Positions

VARIABLES Location, WaitingBeforeBridge

vars == <<Location, WaitingBeforeBridge>>

const_1615720459299211000 == {"r1", "r2"}
const_1615720459299212000 == {"l1", "l2"}
const_1615720459299213000 == {4, 5}
const_1615720459299214000 == 1..8

-----------------------------------------------------------------------------

Cars == CarsRight \union CarsLeft

SetMin(S) == CHOOSE x \in S : \A y \in S : x <= y
SetMax(S) == CHOOSE x \in S : \A y \in S : x >= y

StartPos == SetMin(Positions)
EndPos   == SetMax(Positions)

\* Left cars travel toward increasing positions, right cars toward decreasing ones.
\* The road wraps around, so cars keep crossing the bridge.
NextPos(c) ==
    IF c \in CarsLeft
    THEN IF Location[c] = EndPos THEN StartPos ELSE Location[c] + 1
    ELSE IF Location[c] = StartPos THEN EndPos ELSE Location[c] - 1

\* The position immediately before the bridge for each direction.
BeforeBridge(c) ==
    IF c \in CarsLeft THEN SetMin(Bridge) - 1 ELSE SetMax(Bridge) + 1

Opposite(c) == IF c \in CarsLeft THEN CarsRight ELSE CarsLeft

CarsInBridge == { c \in Cars : Location[c] \in Bridge }

InQueue(c) == \E i \in 1..Len(WaitingBeforeBridge) : WaitingBeforeBridge[i] = c

-----------------------------------------------------------------------------

TypeOK ==
    /\ Location \in [Cars -> Positions]
    /\ \A i \in 1..Len(WaitingBeforeBridge) : WaitingBeforeBridge[i] \in Cars

\* No two cars traveling in opposite directions are on the bridge at once.
NoCollision ==
    \/ CarsInBridge \subseteq CarsLeft
    \/ CarsInBridge \subseteq CarsRight

\* Each waiting car is queued at most once and is located before the bridge.
QueueConsistent ==
    \A i \in 1..Len(WaitingBeforeBridge) :
        /\ Location[WaitingBeforeBridge[i]] = BeforeBridge(WaitingBeforeBridge[i])
        /\ \A j \in 1..Len(WaitingBeforeBridge) :
              i # j => WaitingBeforeBridge[i] # WaitingBeforeBridge[j]

Invariants == TypeOK /\ NoCollision /\ QueueConsistent

-----------------------------------------------------------------------------

Init ==
    /\ Location = [c \in Cars |-> IF c \in CarsLeft THEN StartPos ELSE EndPos]
    /\ WaitingBeforeBridge = <<>>

\* Ordinary movement of a car that is not waiting in front of the bridge.
Move(c) ==
    /\ Location[c] # BeforeBridge(c)
    /\ Location' = [Location EXCEPT ![c] = NextPos(c)]
    /\ IF NextPos(c) = BeforeBridge(c)
       THEN WaitingBeforeBridge' = Append(WaitingBeforeBridge, c)
       ELSE UNCHANGED WaitingBeforeBridge

\* A car at the head of the waiting queue enters the bridge when no
\* opposite-direction car occupies it.
EnterBridge(c) ==
    /\ Location[c] = BeforeBridge(c)
    /\ WaitingBeforeBridge # <<>>
    /\ Head(WaitingBeforeBridge) = c
    /\ \A o \in Opposite(c) : Location[o] \notin Bridge
    /\ Location' = [Location EXCEPT ![c] = NextPos(c)]
    /\ WaitingBeforeBridge' = Tail(WaitingBeforeBridge)

CarStep(c) == Move(c) \/ EnterBridge(c)

Next == \E c \in Cars : CarStep(c)

Fairness == \A c \in Cars : WF_vars(CarStep(c))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------

\* Liveness: every car on the bridge eventually leaves it.
CarsInBridgeExitBridge ==
    \A c \in Cars : (Location[c] \in Bridge) ~> (Location[c] \notin Bridge)

\* Liveness: every car off the bridge eventually gets onto it.
CarsEnterBridge ==
    \A c \in Cars : (Location[c] \notin Bridge) ~> (Location[c] \in Bridge)

=============================================================================