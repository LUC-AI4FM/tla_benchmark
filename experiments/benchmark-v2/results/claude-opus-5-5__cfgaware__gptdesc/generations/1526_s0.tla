---------------------------- MODULE MC ----------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS CarsRight, CarsLeft, Bridge, Positions

VARIABLES Location, WaitingBeforeBridge

vars == <<Location, WaitingBeforeBridge>>

\* Constant definitions used by the model configuration
const_1615720459299211000 == {1, 2}

const_1615720459299212000 == {3, 4}

const_1615720459299213000 == {4, 5}

const_1615720459299214000 == {1, 2, 3, 4, 5, 6, 7, 8}

-------------------------------------------------------------------

Cars == CarsRight \cup CarsLeft

MinP == CHOOSE p \in Positions : \A q \in Positions : p <= q
MaxP == CHOOSE p \in Positions : \A q \in Positions : p >= q

SameSide(c, d) == (c \in CarsRight) = (d \in CarsRight)

\* Right cars move upward and left cars move downward, wrapping around
NextPos(c, p) ==
    IF c \in CarsRight
    THEN IF p = MaxP THEN MinP ELSE p + 1
    ELSE IF p = MinP THEN MaxP ELSE p - 1

StartPos(c) == IF c \in CarsRight THEN MinP ELSE MaxP

OnBridge == {c \in Cars : Location[c] \in Bridge}

RangeSeq(s) == {s[i] : i \in 1..Len(s)}

TypeOK ==
    /\ Location \in [Cars -> Positions]
    /\ WaitingBeforeBridge \in Seq(Cars)

\* Cars travelling in opposite directions are never on the bridge together
BridgeSafety ==
    \A c, d \in OnBridge : SameSide(c, d)

Invariants == TypeOK /\ BridgeSafety

-------------------------------------------------------------------

Init ==
    /\ Location = [c \in Cars |-> StartPos(c)]
    /\ WaitingBeforeBridge = << >>

\* A car moves along the road outside the bridge.
\* When it reaches the position just before the bridge, it joins the queue.
MoveOutside(c) ==
    LET np == NextPos(c, Location[c]) IN
    /\ Location[c] \notin Bridge
    /\ np \notin Bridge
    /\ Location' = [Location EXCEPT ![c] = np]
    /\ WaitingBeforeBridge' =
          IF NextPos(c, np) \in Bridge
          THEN Append(WaitingBeforeBridge, c)
          ELSE WaitingBeforeBridge

\* The car at the head of the queue enters the bridge when no car
\* travelling in the opposite direction is on it.
EnterBridge(c) ==
    /\ WaitingBeforeBridge # << >>
    /\ Head(WaitingBeforeBridge) = c
    /\ \A d \in OnBridge : SameSide(c, d)
    /\ Location' = [Location EXCEPT ![c] = NextPos(c, Location[c])]
    /\ WaitingBeforeBridge' = Tail(WaitingBeforeBridge)

\* A car on the bridge moves forward; it eventually leaves the bridge.
MoveInBridge(c) ==
    /\ Location[c] \in Bridge
    /\ Location' = [Location EXCEPT ![c] = NextPos(c, Location[c])]
    /\ UNCHANGED WaitingBeforeBridge

CarAction(c) == MoveOutside(c) \/ EnterBridge(c) \/ MoveInBridge(c)

Next == \E c \in Cars : CarAction(c)

Spec == Init /\ [][Next]_vars /\ \A c \in Cars : WF_vars(CarAction(c))

-------------------------------------------------------------------

\* Every car on the bridge eventually leaves it
CarsInBridgeExitBridge ==
    \A c \in Cars : (Location[c] \in Bridge) ~> (Location[c] \notin Bridge)

\* Every car off the bridge eventually enters it
CarsEnterBridge ==
    \A c \in Cars : (Location[c] \notin Bridge) ~> (Location[c] \in Bridge)

CarsInfOftenOnBridge ==
    \A car \in CarsRight : []<>(Location[car] \in Bridge)

===================================================================