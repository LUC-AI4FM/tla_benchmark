------------------------------- MODULE EWD840 -------------------------------
(***************************************************************************)
(* TLA+ specification of Dijkstra's EWD 840 algorithm for detecting       *)
(* termination on a ring of N nodes.                                       *)
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
(* Initially the token is black and held by node 0. The other variables   *)
(* may hold arbitrary values of the correct type.                          *)
(***************************************************************************)
Init ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ color \in [Nodes -> Color]
  /\ tpos = 0
  /\ tcolor = "black"

(***************************************************************************)
(* Node 0 may initiate a probe when it has the token and either it is      *)
(* black or the token is black. It passes a white token to node N-1 and   *)
(* paints itself white.                                                    *)
(***************************************************************************)
InitiateProbe ==
  /\ tpos = 0
  /\ tcolor = "black" \/ color[0] = "black"
  /\ tpos' = N-1
  /\ tcolor' = "white"
  /\ active' = active
  /\ color' = [color EXCEPT ![0] = "white"]

(***************************************************************************)
(* A node i different from 0 that possesses the token may pass it on if   *)
(* it is inactive. The token becomes black if node i is black. Node i     *)
(* paints itself white.                                                    *)
(***************************************************************************)
PassToken(i) ==
  /\ tpos = i
  /\ ~ active[i]
  /\ tpos' = i-1
  /\ tcolor' = IF color[i] = "black" THEN "black" ELSE tcolor
  /\ active' = active
  /\ color' = [color EXCEPT ![i] = "white"]

System == InitiateProbe \/ \E i \in Nodes \ {0} : PassToken(i)

(***************************************************************************)
(* Environment actions: an active node may activate another node by       *)
(* sending a message; if the receiver has a higher index the sender turns *)
(* black. An active node may become inactive at any time.                  *)
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
(* Non-properties, useful for validating the specification with TLC.     *)
(***************************************************************************)
NeverBlack == \A i \in Nodes : color[i] # "black"

NeverChangeColor == [][ \A i \in Nodes : UNCHANGED color[i] ]_vars

(***************************************************************************)
(* Main safety property: if there is a white token at node 0 and node 0   *)
(* is white and inactive, then all nodes are inactive.                     *)
(***************************************************************************)
terminationDetected ==
  /\ tpos = 0
  /\ tcolor = "white"
  /\ color[0] = "white"
  /\ ~ active[0]

TerminationDetection ==
  terminationDetected => \A i \in Nodes : ~ active[i]

(***************************************************************************)
(* Liveness: termination is eventually detected.                           *)
(***************************************************************************)
Liveness ==
  (\A i \in Nodes : ~ active[i]) ~> terminationDetected

(***************************************************************************)
(* The algorithm is not live without fairness: with only the safety part  *)
(* of the specification, Liveness may fail.                                *)
(***************************************************************************)
AllNodesTerminateIfNoMessages ==
  <>[][\A i \in Nodes : ~ SendMsg(i)]_vars
    => <>(\A i \in Nodes : ~ active[i])

(***************************************************************************)
(* Dijkstra's inductive invariant.                                         *)
(***************************************************************************)
Inv ==
  \/ P0:: \A i \in Nodes : tpos < i => ~ active[i]
  \/ P1:: \E j \in 0 .. tpos : color[j] = "black"
  \/ P2:: tcolor = "black"

(***************************************************************************)
(* Use the following specification to check that the predicate            *)
(* TypeOK /\ Inv is inductive for EWD 840.                                 *)
(***************************************************************************)
CheckInductiveSpec == TypeOK /\ Inv /\ [][Next]_vars

THEOREM Spec => []TypeOK
THEOREM Spec => []TerminationDetection
THEOREM Spec => Liveness
=============================================================================