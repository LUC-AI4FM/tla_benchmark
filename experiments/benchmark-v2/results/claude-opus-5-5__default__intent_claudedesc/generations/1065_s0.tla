------------------------------- MODULE EWD840 -------------------------------
(***************************************************************************)
(* TLA+ specification of Dijkstra's algorithm for distributed termination *)
(* detection on a ring of N nodes (EWD 840).                               *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

VARIABLES active, color, tpos, tcolor

vars == <<active, color, tpos, tcolor>>

Nodes == 0 .. N-1
Color == {"white", "black"}

TypeOK ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ color \in [Nodes -> Color]
  /\ tpos \in Nodes
  /\ tcolor \in Color

(***************************************************************************)
(* Initially the token is black and held by node 0. Nodes may be active   *)
(* or inactive and white or black.                                         *)
(***************************************************************************)
Init ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ color \in [Nodes -> Color]
  /\ tpos = 0
  /\ tcolor = "black"

(***************************************************************************)
(* Node 0 initiates a new probe when it holds the token and either the    *)
(* token or itself is black.                                               *)
(***************************************************************************)
InitiateProbe ==
  /\ tpos = 0
  /\ tcolor = "black" \/ color[0] = "black"
  /\ tpos' = N-1
  /\ tcolor' = "white"
  /\ color' = [color EXCEPT ![0] = "white"]
  /\ UNCHANGED active

(***************************************************************************)
(* Node i > 0 passes the token to node i-1 once it is inactive. The token *)
(* is blackened if node i is black; node i whitens itself.                 *)
(***************************************************************************)
PassToken(i) ==
  /\ tpos = i
  /\ ~active[i] \/ color[i] = "black" \/ tcolor = "black"
  /\ tpos' = i-1
  /\ tcolor' = IF color[i] = "black" THEN "black" ELSE tcolor
  /\ color' = [color EXCEPT ![i] = "white"]
  /\ UNCHANGED active

System == InitiateProbe \/ \E i \in Nodes \ {0} : PassToken(i)

(***************************************************************************)
(* Underlying computation: an active node may send a message to another   *)
(* node, activating it; sending to a higher-numbered node blackens the    *)
(* sender. An active node may spontaneously become inactive.               *)
(***************************************************************************)
SendMsg(i) ==
  /\ active[i]
  /\ \E j \in Nodes \ {i} :
        /\ active' = [active EXCEPT ![j] = TRUE]
        /\ color' = [color EXCEPT ![i] = IF j > i THEN "black" ELSE @]
  /\ UNCHANGED <<tpos, tcolor>>

Deactivate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<color, tpos, tcolor>>

Environment == \E i \in Nodes : SendMsg(i) \/ Deactivate(i)

Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
allInactive == \A i \in Nodes : ~active[i]

terminationDetected ==
  /\ tpos = 0
  /\ tcolor = "white"
  /\ color[0] = "white"
  /\ ~active[0]

TerminationDetection == terminationDetected => allInactive

Liveness == allInactive ~> terminationDetected

(***************************************************************************)
(* Dijkstra's inductive invariant.                                         *)
(***************************************************************************)
Inv ==
  \/ \A i \in Nodes : tpos < i => ~active[i]
  \/ \E j \in 0 .. tpos : color[j] = "black"
  \/ tcolor = "black"

THEOREM Spec => [](TypeOK /\ Inv /\ TerminationDetection)
THEOREM Spec => Liveness
=============================================================================