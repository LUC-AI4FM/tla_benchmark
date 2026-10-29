--------------------------- MODULE SingleLaneBridge ---------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS CarsRight, CarsLeft, Bridge, Positions

ASSUME CarsRight \cap CarsLeft = {}
ASSUME Bridge \subseteq Positions /\ Positions \subseteq Nat

VARIABLES Location, WaitingBeforeBridge

vars == <<Location, WaitingBeforeBridge>>

Cars == CarsRight \cup CarsLeft

StartPos == CHOOSE min \in Positions : \A p \in Positions : min <= p
EndPos   == CHOOSE max \in Positions : \A p \in Positions : max >= p

ASSUME StartPos \notin Bridge /\ EndPos \notin Bridge

NextLocation(c) ==
    IF c \in CarsRight
    THEN IF Location[c] = EndPos THEN StartPos ELSE Location[c] + 1
    ELSE IF Location[c] = StartPos THEN EndPos ELSE Location[c] - 1

CarsInBridge == { c \in Cars : Location[c] \in Bridge }

InQueue(c) == \E i \in 1..Len(WaitingBeforeBridge) : WaitingBeforeBridge[i] = c

PositionFree(p) == \A d \in Cars : Location[d] # p

Init ==
    /\ Location = [c \in Cars |-> IF c \in CarsRight THEN StartPos ELSE EndPos]
    /\ WaitingBeforeBridge = <<>>

(* Move outside the bridge (not entering it), or move inside / out of the bridge *)
ChangeLocation(c) ==
    /\ \/ /\ Location[c] \notin Bridge
          /\ NextLocation(c) \notin Bridge
       \/ /\ Location[c] \in Bridge
          /\ (NextLocation(c) \in Bridge => PositionFree(NextLocation(c)))
    /\ Location' = [Location EXCEPT ![c] = NextLocation(c)]
    /\ UNCHANGED WaitingBeforeBridge

(* Car arrives just before the bridge and starts waiting *)
WaitBeforeBridge(c) ==
    /\ Location[c] \notin Bridge
    /\ NextLocation(c) \in Bridge
    /\ ~InQueue(c)
    /\ WaitingBeforeBridge' = Append(WaitingBeforeBridge, c)
    /\ UNCHANGED Location

Move(c) == ChangeLocation(c) \/ WaitBeforeBridge(c)

(* The first waiting car enters the bridge if no car goes the opposite way *)
EnterBridge ==
    /\ Len(WaitingBeforeBridge) > 0
    /\ LET c == Head(WaitingBeforeBridge)
       IN  /\ IF c \in CarsRight
                 THEN \A d \in CarsInBridge : d \in CarsRight
                 ELSE \A d \in CarsInBridge : d \in CarsLeft
           /\ PositionFree(NextLocation(c))
           /\ Location' = [Location EXCEPT ![c] = NextLocation(c)]
           /\ WaitingBeforeBridge' = Tail(WaitingBeforeBridge)

Next == EnterBridge \/ \E c \in Cars : Move(c)

Fairness ==
    /\ \A c \in Cars : WF_vars(Move(c))
    /\ WF_vars(EnterBridge)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
TypeOK ==
    /\ Location \in [Cars -> Positions]
    /\ \A i \in 1..Len(WaitingBeforeBridge) : WaitingBeforeBridge[i] \in Cars

NoOppositeDirections ==
    ~ (\E r \in CarsRight, l \in CarsLeft :
          Location[r] \in Bridge /\ Location[l] \in Bridge)

NoCollision ==
    \A a, b \in CarsInBridge : a # b => Location[a] # Location[b]

Invariants == TypeOK /\ NoOppositeDirections /\ NoCollision

CarsEnterBridge ==
    \A c \in Cars : (Location[c] \notin Bridge) ~> (Location[c] \in Bridge)

CarsInBridgeExitBridge ==
    \A c \in Cars : (Location[c] \in Bridge) ~> (Location[c] \notin Bridge)
=============================================================================