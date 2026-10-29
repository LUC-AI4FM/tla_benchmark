--------------------------- MODULE SingleLaneBridge ---------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS CarsRight, CarsLeft, Bridge, Positions

VARIABLES Location, WaitingBeforeBridge

vars == <<Location, WaitingBeforeBridge>>

-----------------------------------------------------------------------------
(* Model values used by the model-checking configuration *)

const_1615720459299211000 == {"r1", "r2"}
const_1615720459299212000 == {"l1"}
const_1615720459299213000 == {3, 4}
const_1615720459299214000 == 1..6

-----------------------------------------------------------------------------
Cars == CarsRight \cup CarsLeft

StartPos    == CHOOSE p \in Positions : \A q \in Positions : p <= q
EndPos      == CHOOSE p \in Positions : \A q \in Positions : p >= q
StartBridge == CHOOSE p \in Bridge : \A q \in Bridge : p <= q
EndBridge   == CHOOSE p \in Bridge : \A q \in Bridge : p >= q

RightEntry == StartBridge - 1
LeftEntry  == EndBridge + 1

ASSUME CarsRight \cap CarsLeft = {}
ASSUME Cars # {}
ASSUME Positions = StartPos..EndPos
ASSUME Bridge \subseteq Positions
ASSUME Bridge = StartBridge..EndBridge
ASSUME StartPos < StartBridge /\ EndBridge < EndPos
ASSUME Cardinality(CarsRight) < Cardinality(Positions)
ASSUME Cardinality(CarsLeft) < Cardinality(Positions)

Dir(c)   == IF c \in CarsRight THEN CarsRight ELSE CarsLeft
Entry(c) == IF c \in CarsRight THEN RightEntry ELSE LeftEntry

NextPos(c) ==
    IF c \in CarsRight
    THEN IF Location[c] = EndPos THEN StartPos ELSE Location[c] + 1
    ELSE IF Location[c] = StartPos THEN EndPos ELSE Location[c] - 1

CarsInBridge == { c \in Cars : Location[c] \in Bridge }

WaitingSet == { WaitingBeforeBridge[i] : i \in 1..Len(WaitingBeforeBridge) }

(* Off the bridge, the road has one lane per direction; on the bridge, a
   single lane is shared by both directions. *)
Free(c, p) ==
    IF p \in Bridge
    THEN \A d \in Cars \ {c} : Location[d] # p
    ELSE \A d \in Dir(c) \ {c} : Location[d] # p

-----------------------------------------------------------------------------
InitPositions == Positions \ (Bridge \cup {RightEntry, LeftEntry})

Init ==
    /\ Location \in [Cars -> InitPositions]
    /\ \A c, d \in Cars : (c # d /\ Dir(c) = Dir(d)) => Location[c] # Location[d]
    /\ WaitingBeforeBridge = <<>>

Move(c) ==
    LET p == NextPos(c) IN
    /\ Free(c, p)
    /\ IF Location[c] = Entry(c)
       THEN /\ WaitingBeforeBridge # <<>>
            /\ Head(WaitingBeforeBridge) = c
            /\ \A d \in CarsInBridge : d \in Dir(c)
            /\ WaitingBeforeBridge' = Tail(WaitingBeforeBridge)
       ELSE IF p = Entry(c)
            THEN WaitingBeforeBridge' = Append(WaitingBeforeBridge, c)
            ELSE UNCHANGED WaitingBeforeBridge
    /\ Location' = [Location EXCEPT ![c] = p]

Next == \E c \in Cars : Move(c)

Fairness == \A c \in Cars : WF_vars(Move(c))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety *)

TypeOK ==
    /\ Location \in [Cars -> Positions]
    /\ WaitingBeforeBridge \in Seq(Cars)

\* No head-on collision: all cars on the bridge travel in the same direction
NoHeadOnCollision ==
    \A c, d \in CarsInBridge : Dir(c) = Dir(d)

\* No two cars share a position on the bridge, nor in the same lane
NoPositionConflict ==
    \A c, d \in Cars :
        (c # d /\ (Location[c] \in Bridge \/ Dir(c) = Dir(d)))
            => Location[c] # Location[d]

\* The waiting queue contains exactly the cars waiting at their entry, once each
QueueConsistent ==
    /\ Len(WaitingBeforeBridge) = Cardinality(WaitingSet)
    /\ \A c \in Cars : (Location[c] = Entry(c)) <=> (c \in WaitingSet)

Invariants ==
    /\ TypeOK
    /\ NoHeadOnCollision
    /\ NoPositionConflict
    /\ QueueConsistent

\* No overtaking: cars only advance one step into a free slot of their lane
NoOvertaking ==
    [][\A c \in Cars :
          Location'[c] = Location[c]
          \/ (Location'[c] = NextPos(c) /\ Free(c, NextPos(c)))]_vars

\* Deadlock freedom: some car can always move
NoDeadlock == \E c \in Cars : ENABLED Move(c)

-----------------------------------------------------------------------------
(* Liveness *)

CarsInBridgeExitBridge ==
    \A c \in Cars : (Location[c] \in Bridge) ~> (Location[c] \notin Bridge)

CarsEnterBridge ==
    \A c \in Cars : (Location[c] \notin Bridge) ~> (Location[c] \in Bridge)

CarsInfOftenOnBridge ==
    \A c \in Cars : []<>(Location[c] \in Bridge)

NoStarvation ==
    \A c \in Cars : (Location[c] = Entry(c)) ~> (Location[c] \in Bridge)

=============================================================================