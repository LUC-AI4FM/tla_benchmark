---------------------------- MODULE MC ----------------------------
(***************************************************************************)
(* Model-checking configuration for a single-lane bridge system.           *)
(* Cars approaching from the right travel toward decreasing positions and  *)
(* cars approaching from the left travel toward increasing positions.      *)
(* The banks have two lanes, one per direction. The bridge is a single     *)
(* lane, so cars travelling in opposite directions may never be on it at   *)
(* the same time. A FIFO queue of cars waiting in front of the bridge      *)
(* decides who enters next, which ensures fairness. When a car reaches the *)
(* end of the road it wraps around, so it crosses the bridge again and     *)
(* again.                                                                  *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS CarsRight, CarsLeft, Bridge, Positions

VARIABLES Location, WaitingBeforeBridge

vars == <<Location, WaitingBeforeBridge>>

---------------------------------------------------------------------------
(* Model parameterisation (explicit set enumerations), to be substituted   *)
(* for the constants in the TLC configuration, e.g.                        *)
(*   CONSTANT CarsRight <- const_CarsRight                                 *)
const_CarsRight == {1, 2}
const_CarsLeft  == {5, 6}
const_Bridge    == {4, 5}
const_Positions == {1, 2, 3, 4, 5, 6, 7, 8}

---------------------------------------------------------------------------
Cars == CarsRight \cup CarsLeft

Min(S) == CHOOSE x \in S : \A y \in S : x <= y
Max(S) == CHOOSE x \in S : \A y \in S : y <= x

MinPos      == Min(Positions)
MaxPos      == Max(Positions)
StartBridge == Min(Bridge)
EndBridge   == Max(Bridge)

ASSUME /\ CarsRight \cap CarsLeft = {}
       /\ Bridge \subseteq Positions
       /\ Positions \subseteq Nat

Opposite(c) == IF c \in CarsRight THEN CarsLeft ELSE CarsRight
SameDir(c, d) == (c \in CarsRight) = (d \in CarsRight)

\* Position from which a car waits to enter the bridge.
BeforeBridge(c) == IF c \in CarsRight THEN EndBridge + 1 ELSE StartBridge - 1

\* Next position of a car along its direction of travel (wrapping around).
NextPos(c) ==
  IF c \in CarsRight
    THEN IF Location[c] = MinPos THEN MaxPos ELSE Location[c] - 1
    ELSE IF Location[c] = MaxPos THEN MinPos ELSE Location[c] + 1

\* Position p is free for car c. On the bridge, a position may hold only one
\* car. On the banks, each direction has its own lane.
Free(c, p) ==
  \A d \in Cars \ {c} :
     Location[d] = p => (p \notin Bridge /\ ~SameDir(c, d))

---------------------------------------------------------------------------
TypeOK ==
  /\ Location \in [Cars -> Positions]
  /\ WaitingBeforeBridge \in Seq(Cars)

Init ==
  /\ Location \in { f \in [Cars -> Positions] :
                      /\ \A c \in CarsRight : f[c] > EndBridge + 1
                      /\ \A c \in CarsLeft  : f[c] < StartBridge - 1
                      /\ \A c, d \in Cars :
                           (c # d /\ SameDir(c, d)) => f[c] # f[d] }
  /\ WaitingBeforeBridge = <<>>

Move(c) ==
  LET p == NextPos(c) IN
    /\ Free(c, p)
    /\ IF p \in Bridge /\ Location[c] \notin Bridge
         THEN \* entering the bridge: must be first in line, bridge clear
              /\ WaitingBeforeBridge # <<>>
              /\ Head(WaitingBeforeBridge) = c
              /\ \A d \in Opposite(c) : Location[d] \notin Bridge
              /\ WaitingBeforeBridge' = Tail(WaitingBeforeBridge)
         ELSE IF p = BeforeBridge(c)
                THEN WaitingBeforeBridge' = Append(WaitingBeforeBridge, c)
                ELSE UNCHANGED WaitingBeforeBridge
    /\ Location' = [Location EXCEPT ![c] = p]

Next == \E c \in Cars : Move(c)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A c \in Cars : WF_vars(Move(c))

---------------------------------------------------------------------------
(* Safety *)
BridgeSafety ==
  ~ \E r \in CarsRight, l \in CarsLeft :
       Location[r] \in Bridge /\ Location[l] \in Bridge

NoCollisionOnBridge ==
  \A c, d \in Cars : (c # d /\ Location[c] \in Bridge) => Location[c] # Location[d]

(* Liveness: every car from the right is infinitely often on the bridge *)
CarsInfOftenOnBridge ==
  \A car \in CarsRight : []<>(Location[car] \in Bridge)

===========================================================================