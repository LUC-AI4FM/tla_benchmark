---------------------------- MODULE MC_SingleLaneBridge ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CarsRight, CarsLeft, Bridge, Positions

VARIABLES Location, WaitingBeforeBridge

vars == <<Location, WaitingBeforeBridge>>

\* Model-checking configuration values
const_CarsRight == {"r1", "r2"}
const_CarsLeft  == {"l1", "l2"}
const_Bridge    == {4, 5}
const_Positions == 1..8

ASSUME /\ CarsRight \cap CarsLeft = {}
       /\ Bridge \subseteq Positions
       /\ Positions \subseteq Nat

Cars == CarsRight \cup CarsLeft

Max(S) == CHOOSE x \in S : \A y \in S : y <= x
Min(S) == CHOOSE x \in S : \A y \in S : x <= y

\* Right cars travel from high to low positions, left cars from low to high.
StartPos(c) == IF c \in CarsRight THEN Max(Positions) ELSE Min(Positions)

\* Position immediately before the bridge for each direction.
BeforeBridge(c) == IF c \in CarsRight THEN Max(Bridge) + 1 ELSE Min(Bridge) - 1

NextLocation(c) ==
    IF c \in CarsRight
    THEN IF Location[c] = Min(Positions) THEN Max(Positions) ELSE Location[c] - 1
    ELSE IF Location[c] = Max(Positions) THEN Min(Positions) ELSE Location[c] + 1

SameDirection(a, b) == \/ a \in CarsRight /\ b \in CarsRight
                       \/ a \in CarsLeft  /\ b \in CarsLeft

CarsOnBridge == {c \in Cars : Location[c] \in Bridge}

------------------------------------------------------------------------------------

Init == /\ Location = [c \in Cars |-> StartPos(c)]
        /\ WaitingBeforeBridge = << >>

\* A car moves along the road (not across the bridge entrance).
Move(c) ==
    /\ Location[c] # BeforeBridge(c)
    /\ Location' = [Location EXCEPT ![c] = NextLocation(c)]
    /\ WaitingBeforeBridge' =
          IF NextLocation(c) = BeforeBridge(c)
          THEN Append(WaitingBeforeBridge, c)
          ELSE WaitingBeforeBridge

\* The first waiting car enters the bridge if no car from the other direction is on it.
EnterBridge ==
    /\ WaitingBeforeBridge # << >>
    /\ LET c == Head(WaitingBeforeBridge) IN
         /\ \A d \in CarsOnBridge : SameDirection(c, d)
         /\ Location' = [Location EXCEPT ![c] = NextLocation(c)]
         /\ WaitingBeforeBridge' = Tail(WaitingBeforeBridge)

Next == \/ \E c \in Cars : Move(c)
        \/ EnterBridge

Fairness == /\ \A c \in Cars : WF_vars(Move(c))
            /\ WF_vars(EnterBridge)

Spec == Init /\ [][Next]_vars /\ Fairness

------------------------------------------------------------------------------------
\* Safety

TypeOK == /\ Location \in [Cars -> Positions]
          /\ WaitingBeforeBridge \in Seq(Cars)

CollisionFree == \A a, b \in CarsOnBridge : SameDirection(a, b)

Invariants == TypeOK /\ CollisionFree

\* Liveness

CarsInBridgeExitBridge ==
    \A c \in Cars : (Location[c] \in Bridge) ~> (Location[c] \notin Bridge)

CarsEnterBridge ==
    \A c \in Cars : (Location[c] = BeforeBridge(c)) ~> (Location[c] \in Bridge)

CarsInfOftenOnBridge ==
    \A c \in CarsRight : []<>(Location[c] \in Bridge)

THEOREM Spec => []Invariants
THEOREM Spec => (CarsInBridgeExitBridge /\ CarsEnterBridge /\ CarsInfOftenOnBridge)
====================================================================================