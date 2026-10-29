------------------------------- MODULE MC -------------------------------
(***************************************************************************)
(* Model-checking configuration for a single-lane bridge system.           *)
(* The bridge behaviour is defined inline so that this module is           *)
(* self-contained and parses on its own.                                   *)
(*                                                                         *)
(* Right cars move toward lower positions and left cars move toward        *)
(* higher positions. Both kinds of car wrap around at the ends of the      *)
(* road. Off the bridge the road has two lanes, so cars going in opposite  *)
(* directions may pass each other there. The bridge has one lane, so cars  *)
(* going in opposite directions may never be on it at the same time.       *)
(* A FIFO queue of cars waiting at the bridge entrances keeps the          *)
(* admission order fair.                                                   *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS CarsRight, CarsLeft, Bridge, Positions

VARIABLES Location, WaitingBeforeBridge

vars == <<Location, WaitingBeforeBridge>>

(***************************************************************************)
(* Constant definitions used by the model configuration (TLC .cfg file):   *)
(*   CarsRight <- const_CarsRight                                          *)
(*   CarsLeft  <- const_CarsLeft                                           *)
(*   Bridge    <- const_Bridge                                             *)
(*   Positions <- const_Positions                                          *)
(***************************************************************************)
const_CarsRight == {"r1", "r2"}

const_CarsLeft == {"l1", "l2"}

const_Bridge == {4, 5}

const_Positions == {1, 2, 3, 4, 5, 6, 7, 8}

-----------------------------------------------------------------------------
(* Helper definitions *)

Cars == CarsRight \cup CarsLeft

SetMin(S) == CHOOSE x \in S : \A y \in S : x <= y
SetMax(S) == CHOOSE x \in S : \A y \in S : x >= y

FirstPos == SetMin(Positions)
LastPos  == SetMax(Positions)

SameDirection(c) == IF c \in CarsRight THEN CarsRight ELSE CarsLeft
Opposite(c)      == IF c \in CarsRight THEN CarsLeft  ELSE CarsRight

NextLocation(c) ==
    IF c \in CarsRight
       THEN IF Location[c] = FirstPos THEN LastPos ELSE Location[c] - 1
       ELSE IF Location[c] = LastPos  THEN FirstPos ELSE Location[c] + 1

OnBridge(c) == Location[c] \in Bridge

InQueue(c) == \E i \in 1..Len(WaitingBeforeBridge) : WaitingBeforeBridge[i] = c

NextFree(c) == \A d \in SameDirection(c) \ {c} : Location[d] # NextLocation(c)

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ Location \in
         { f \in [Cars -> Positions \ Bridge] :
             /\ \A c \in CarsRight : f[c] > SetMax(Bridge)
             /\ \A c \in CarsLeft  : f[c] < SetMin(Bridge)
             /\ \A c, d \in Cars :
                   (c # d /\ f[c] = f[d]) => ((c \in CarsRight) # (d \in CarsRight)) }
    /\ WaitingBeforeBridge = <<>>

-----------------------------------------------------------------------------
(* Actions *)

(* A car arrives at the bridge entrance and joins the waiting queue. *)
Approach(c) ==
    /\ ~OnBridge(c)
    /\ NextLocation(c) \in Bridge
    /\ ~InQueue(c)
    /\ WaitingBeforeBridge' = Append(WaitingBeforeBridge, c)
    /\ UNCHANGED Location

(* The car at the head of the queue enters the bridge when no car going    *)
(* the opposite direction is on it.                                        *)
Enter(c) ==
    /\ ~OnBridge(c)
    /\ NextLocation(c) \in Bridge
    /\ WaitingBeforeBridge # <<>>
    /\ Head(WaitingBeforeBridge) = c
    /\ \A d \in Opposite(c) : ~OnBridge(d)
    /\ NextFree(c)
    /\ Location' = [Location EXCEPT ![c] = NextLocation(c)]
    /\ WaitingBeforeBridge' = Tail(WaitingBeforeBridge)

(* A car moves along the road, along the bridge, or off the bridge. *)
MoveOn(c) ==
    /\ OnBridge(c) \/ NextLocation(c) \notin Bridge
    /\ NextFree(c)
    /\ Location' = [Location EXCEPT ![c] = NextLocation(c)]
    /\ UNCHANGED WaitingBeforeBridge

Move(c) == Approach(c) \/ Enter(c) \/ MoveOn(c)

Next == \E c \in Cars : Move(c)

Fairness ==
    \A c \in Cars :
        /\ WF_vars(Approach(c))
        /\ SF_vars(Enter(c))
        /\ WF_vars(MoveOn(c))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety invariants *)

TypeOK ==
    /\ Location \in [Cars -> Positions]
    /\ WaitingBeforeBridge \in Seq(Cars)

(* Two cars going the same direction never share a position. *)
NoCollision ==
    \A c, d \in Cars :
        (c # d /\ SameDirection(c) = SameDirection(d)) => Location[c] # Location[d]

(* Cars going opposite directions are never on the bridge at the same time. *)
OneDirectionOnBridge ==
    ~(\E r \in CarsRight, l \in CarsLeft : OnBridge(r) /\ OnBridge(l))

(* A car appears in the waiting queue at most once. *)
QueueNoDuplicates ==
    \A i, j \in 1..Len(WaitingBeforeBridge) :
        (i # j) => WaitingBeforeBridge[i] # WaitingBeforeBridge[j]

-----------------------------------------------------------------------------
(* Liveness property *)

CarsInfOftenOnBridge ==
    \A car \in CarsRight : []<>(Location[car] \in Bridge)

=============================================================================