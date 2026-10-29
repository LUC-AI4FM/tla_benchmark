---------------------------- MODULE MC ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CarsRight, CarsLeft, Bridge, Positions

VARIABLES Location, WaitingBeforeBridge

vars == << Location, WaitingBeforeBridge >>

\* ---------------- Concrete constant definitions for TLC ----------------

const_1615720459299211000 == {"r1", "r2"}

const_1615720459299212000 == {"l1", "l2"}

const_1615720459299213000 == {4, 5}

const_1615720459299214000 == 1..8

\* ---------------- Single-lane bridge model ----------------

Cars == CarsRight \cup CarsLeft

SetMin(S) == CHOOSE x \in S : \A y \in S : x <= y
SetMax(S) == CHOOSE x \in S : \A y \in S : x >= y

StartPos(c) == IF c \in CarsRight THEN SetMin(Positions) ELSE SetMax(Positions)
EndPos(c)   == IF c \in CarsRight THEN SetMax(Positions) ELSE SetMin(Positions)

BeforeBridge(c) == IF c \in CarsRight THEN SetMin(Bridge) - 1 ELSE SetMax(Bridge) + 1
BridgeEntry(c)  == IF c \in CarsRight THEN SetMin(Bridge) ELSE SetMax(Bridge)

NextPos(c) ==
    IF Location[c] = EndPos(c)
        THEN StartPos(c)
        ELSE IF c \in CarsRight THEN Location[c] + 1 ELSE Location[c] - 1

SameDirection(c) == IF c \in CarsRight THEN CarsRight ELSE CarsLeft

CarsInBridge == { c \in Cars : Location[c] \in Bridge }

Range(s) == { s[i] : i \in DOMAIN s }

Init ==
    /\ Location = [c \in Cars |-> StartPos(c)]
    /\ WaitingBeforeBridge = << >>

\* A car outside the bridge advances; if it reaches the position just
\* before the bridge, it joins the waiting queue.
MoveOutsideBridge ==
    \E c \in Cars :
        /\ Location[c] \notin Bridge
        /\ Location[c] # BeforeBridge(c)
        /\ Location' = [Location EXCEPT ![c] = NextPos(c)]
        /\ WaitingBeforeBridge' =
              IF NextPos(c) = BeforeBridge(c)
                 THEN Append(WaitingBeforeBridge, c)
                 ELSE WaitingBeforeBridge

\* The car at the head of the queue enters the bridge when the bridge is
\* empty or holds only cars travelling in the same direction.
CarsEnterBridge ==
    /\ WaitingBeforeBridge # << >>
    /\ LET c == Head(WaitingBeforeBridge) IN
         /\ CarsInBridge \subseteq SameDirection(c)
         /\ \A d \in CarsInBridge : Location[d] # BridgeEntry(c)
         /\ Location' = [Location EXCEPT ![c] = BridgeEntry(c)]
         /\ WaitingBeforeBridge' = Tail(WaitingBeforeBridge)

\* A car on the bridge moves forward, possibly leaving the bridge.
CarsInBridgeExitBridge ==
    \E c \in CarsInBridge :
        /\ \A d \in CarsInBridge \ {c} : Location[d] # NextPos(c)
        /\ Location' = [Location EXCEPT ![c] = NextPos(c)]
        /\ UNCHANGED WaitingBeforeBridge

Next ==
    \/ MoveOutsideBridge
    \/ CarsEnterBridge
    \/ CarsInBridgeExitBridge

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)

\* ---------------- Invariants ----------------

TypeOK ==
    /\ Location \in [Cars -> Positions]
    /\ WaitingBeforeBridge \in Seq(Cars)

NoOppositeCarsOnBridge ==
    \/ CarsInBridge \subseteq CarsRight
    \/ CarsInBridge \subseteq CarsLeft

NoCollisionOnBridge ==
    \A c, d \in CarsInBridge : c # d => Location[c] # Location[d]

WaitingCarsAreBeforeBridge ==
    \A c \in Range(WaitingBeforeBridge) : Location[c] = BeforeBridge(c)

Invariants ==
    /\ TypeOK
    /\ NoOppositeCarsOnBridge
    /\ NoCollisionOnBridge
    /\ WaitingCarsAreBeforeBridge

=============================================================================