------------------------- MODULE SingleLaneBridge -------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS CarsRight, CarsLeft, Bridge, Positions

VARIABLES Location, WaitingBeforeBridge

vars == <<Location, WaitingBeforeBridge>>

(* Model values used to instantiate the constants *)
const_1615720459299211000 == {"r1", "r2"}
const_1615720459299212000 == {"l1", "l2"}
const_1615720459299213000 == 4..5
const_1615720459299214000 == 1..8

-----------------------------------------------------------------------------
Cars == CarsRight \cup CarsLeft

StartPos    == CHOOSE p \in Positions : \A q \in Positions : p <= q
EndPos      == CHOOSE p \in Positions : \A q \in Positions : p >= q
StartBridge == CHOOSE p \in Bridge : \A q \in Bridge : p <= q
EndBridge   == CHOOSE p \in Bridge : \A q \in Bridge : p >= q

ASSUME CarsRight \cap CarsLeft = {}
ASSUME Cars # {}
ASSUME Positions = StartPos..EndPos
ASSUME Bridge \subseteq Positions /\ Bridge = StartBridge..EndBridge
ASSUME StartPos < StartBridge - 1 /\ EndBridge + 1 < EndPos

(* Right cars travel towards smaller positions, left cars towards larger
   positions. Outside the bridge each direction has its own lane; the bridge
   is a single shared lane. Roads wrap around so cars keep returning.      *)
RMove(p) == IF p > StartPos THEN p - 1 ELSE EndPos
LMove(p) == IF p < EndPos   THEN p + 1 ELSE StartPos

NextLocation(car) ==
    IF car \in CarsRight THEN RMove(Location[car]) ELSE LMove(Location[car])

SameDir(c1, c2) ==
    \/ c1 \in CarsRight /\ c2 \in CarsRight
    \/ c1 \in CarsLeft  /\ c2 \in CarsLeft

(* Position immediately before the bridge for the car's direction *)
PreBridge(car) == IF car \in CarsRight THEN EndBridge + 1 ELSE StartBridge - 1

CarsInBridge == {c \in Cars : Location[c] \in Bridge}

(* Position p is free for car: no same-lane car there, and on the bridge no car at all *)
Free(car, p) ==
    \A c \in Cars \ {car} :
        Location[c] = p => (p \notin Bridge /\ ~SameDir(c, car))

NoOppositeOnBridge(car) ==
    \A c \in CarsInBridge : SameDir(c, car)

InitPos == Positions \ (Bridge \cup {StartBridge - 1, EndBridge + 1})

Init ==
    /\ Location \in [Cars -> InitPos]
    /\ \A c1, c2 \in Cars :
          (c1 # c2 /\ SameDir(c1, c2)) => Location[c1] # Location[c2]
    /\ WaitingBeforeBridge = <<>>

Move(car) ==
    LET np == NextLocation(car) IN
    /\ Free(car, np)
    /\ IF Location[car] = PreBridge(car)
         THEN (* entering the bridge: FIFO order and mutual exclusion *)
              /\ WaitingBeforeBridge # <<>>
              /\ Head(WaitingBeforeBridge) = car
              /\ NoOppositeOnBridge(car)
              /\ WaitingBeforeBridge' = Tail(WaitingBeforeBridge)
         ELSE IF np = PreBridge(car)
                THEN WaitingBeforeBridge' = Append(WaitingBeforeBridge, car)
                ELSE UNCHANGED WaitingBeforeBridge
    /\ Location' = [Location EXCEPT ![car] = np]

Next == \E car \in Cars : Move(car)

Fairness == \A car \in Cars : WF_vars(Move(car))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
TypeOK ==
    /\ Location \in [Cars -> Positions]
    /\ WaitingBeforeBridge \in Seq(Cars)

(* Boundedness *)
Bounded == \A c \in Cars : Location[c] \in Positions

(* No two vehicles share a position (per lane outside, at all on the bridge) *)
NoCollision ==
    \A c1, c2 \in Cars :
        (c1 # c2 /\ Location[c1] = Location[c2]) =>
            (Location[c1] \notin Bridge /\ ~SameDir(c1, c2))

(* No opposite-direction vehicles simultaneously on the bridge *)
BridgeSafety ==
    \/ CarsInBridge \subseteq CarsRight
    \/ CarsInBridge \subseteq CarsLeft

(* The waiting queue contains exactly the cars waiting before the bridge *)
QueueOK ==
    /\ \A i, j \in 1..Len(WaitingBeforeBridge) :
          i # j => WaitingBeforeBridge[i] # WaitingBeforeBridge[j]
    /\ \A c \in Cars :
          (Location[c] = PreBridge(c)) <=>
             (\E i \in 1..Len(WaitingBeforeBridge) : WaitingBeforeBridge[i] = c)

Invariants ==
    /\ TypeOK
    /\ Bounded
    /\ NoCollision
    /\ BridgeSafety
    /\ QueueOK

-----------------------------------------------------------------------------
(* Progress properties *)
CarsInBridgeExitBridge ==
    \A car \in Cars : (Location[car] \in Bridge) ~> (Location[car] \notin Bridge)

CarsEnterBridge ==
    \A car \in Cars : (Location[car] \notin Bridge) ~> (Location[car] \in Bridge)

=============================================================================