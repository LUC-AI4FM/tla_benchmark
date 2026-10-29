--------------------------- MODULE SingleLaneBridge ---------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS CarsRight, CarsLeft, Bridge, Positions

VARIABLES Location, WaitingBeforeBridge

vars == <<Location, WaitingBeforeBridge>>

\* Concrete model values bound by the configuration
const_1615720459299211000 == {5, 6}
const_1615720459299212000 == {1, 2}
const_1615720459299213000 == {4, 5}
const_1615720459299214000 == 1..8

Cars == CarsRight \union CarsLeft

StartPos    == CHOOSE min \in Positions : \A p \in Positions : min <= p
EndPos      == CHOOSE max \in Positions : \A p \in Positions : max >= p
StartBridge == CHOOSE min \in Bridge : \A p \in Bridge : min <= p
EndBridge   == CHOOSE max \in Bridge : \A p \in Bridge : max >= p

ASSUME CarsRight \cap CarsLeft = {}
ASSUME Bridge \subseteq Positions
ASSUME StartPos < StartBridge /\ EndBridge < EndPos

\* Left cars travel towards increasing positions, right cars towards decreasing
\* positions. The roadway is circular so cars repeatedly come back to the bridge.
LNext(p) == IF p = EndPos THEN StartPos ELSE p + 1
RNext(p) == IF p = StartPos THEN EndPos ELSE p - 1

LWait == StartBridge - 1
RWait == EndBridge + 1

SameDir(c) == IF c \in CarsLeft THEN CarsLeft ELSE CarsRight
OtherDir(c) == IF c \in CarsLeft THEN CarsRight ELSE CarsLeft

NextLocation(c) == IF c \in CarsLeft THEN LNext(Location[c]) ELSE RNext(Location[c])
WaitPos(c) == IF c \in CarsLeft THEN LWait ELSE RWait

CarsOnBridge == {c \in Cars : Location[c] \in Bridge}

TypeOK ==
    /\ Location \in [Cars -> Positions]
    /\ WaitingBeforeBridge \in Seq(Cars)

Init ==
    /\ Location \in { f \in [Cars -> Positions \ (Bridge \union {LWait, RWait})] :
                        \A a, b \in Cars :
                           (a # b /\ SameDir(a) = SameDir(b)) => f[a] # f[b] }
    /\ WaitingBeforeBridge = <<>>

Move(c) ==
    LET np == NextLocation(c) IN
    /\ \A d \in SameDir(c) \ {c} : Location[d] # np
    /\ IF np \in Bridge /\ Location[c] \notin Bridge
         THEN /\ WaitingBeforeBridge # <<>>
              /\ Head(WaitingBeforeBridge) = c
              /\ \A d \in OtherDir(c) : Location[d] \notin Bridge
              /\ WaitingBeforeBridge' = Tail(WaitingBeforeBridge)
         ELSE IF np = WaitPos(c)
                THEN WaitingBeforeBridge' = Append(WaitingBeforeBridge, c)
                ELSE UNCHANGED WaitingBeforeBridge
    /\ Location' = [Location EXCEPT ![c] = np]

Next == \E c \in Cars : Move(c)

Fairness == \A c \in Cars : SF_vars(Move(c))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety
NoHeadOnCollision ==
    ~ (\E a \in CarsLeft, b \in CarsRight : Location[a] \in Bridge /\ Location[b] \in Bridge)

NoOverlap ==
    \A a, b \in Cars :
        (a # b /\ (SameDir(a) = SameDir(b) \/ Location[a] \in Bridge))
            => Location[a] # Location[b]

Invariants == TypeOK /\ NoHeadOnCollision /\ NoOverlap

\* Liveness
CarsInBridgeExitBridge ==
    \A c \in Cars : (Location[c] \in Bridge) ~> (Location[c] \notin Bridge)

CarsEnterBridge ==
    \A c \in Cars : (Location[c] \notin Bridge) ~> (Location[c] \in Bridge)

CarsInfOftenOnBridge ==
    \A c \in Cars : []<>(Location[c] \in Bridge)

=============================================================================