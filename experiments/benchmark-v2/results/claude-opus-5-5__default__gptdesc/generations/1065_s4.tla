------------------------------- MODULE EWD840 -------------------------------
(***************************************************************************)
(* Dijkstra's EWD 840 algorithm for detecting termination on a ring of N  *)
(* nodes. Nodes are numbered 0..N-1. Node 0 is the master node that        *)
(* initiates probes. The token travels from node i to node i-1.            *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

VARIABLES active, color, tpos, tcolor

vars == <<active, color, tpos, tcolor>>

Node == 0 .. N-1
Color == {"white", "black"}

TypeOK ==
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  /\ tpos \in Node
  /\ tcolor \in Color

(***************************************************************************)
(* Initially the token is black, so that the first probe cannot           *)
(* immediately declare termination. Other variables are arbitrary.        *)
(***************************************************************************)
Init ==
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  /\ tpos \in Node
  /\ tcolor = "black"

(***************************************************************************)
(* Node 0 initiates a new probe when it holds the token and the previous  *)
(* round was inconclusive (token black or node 0 black).                  *)
(***************************************************************************)
InitiateProbe ==
  /\ tpos = 0
  /\ (tcolor = "black" \/ color[0] = "black")
  /\ tpos' = N-1
  /\ tcolor' = "white"
  /\ active' = active
  /\ color' = [color EXCEPT ![0] = "white"]

(***************************************************************************)
(* Node i > 0 passes the token to node i-1 when it is inactive, or when   *)
(* the round is already known to be inconclusive.                          *)
(***************************************************************************)
PassToken(i) ==
  /\ tpos = i
  /\ (~ active[i] \/ color[i] = "black" \/ tcolor = "black")
  /\ tpos' = i-1
  /\ tcolor' = IF color[i] = "black" THEN "black" ELSE tcolor
  /\ active' = active
  /\ color' = [color EXCEPT ![i] = "white"]

System == InitiateProbe \/ \E i \in Node \ {0} : PassToken(i)

(***************************************************************************)
(* Environment actions: an active node may send a message to another node, *)
(* activating it; sending to a node with a higher number blackens the      *)
(* sender. An active node may become inactive.                             *)
(***************************************************************************)
SendMsg(i) ==
  /\ active[i]
  /\ \E j \in Node \ {i} :
        /\ active' = [active EXCEPT ![j] = TRUE]
        /\ color' = [color EXCEPT ![i] = IF j > i THEN "black" ELSE @]
  /\ UNCHANGED <<tpos, tcolor>>

Deactivate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<color, tpos, tcolor>>

Environment == \E i \in Node : SendMsg(i) \/ Deactivate(i)

Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Correctness properties.                                                 *)
(***************************************************************************)
terminationDetected ==
  /\ tpos = 0
  /\ tcolor = "white"
  /\ color[0] = "white"
  /\ ~ active[0]

AllInactive == \A i \in Node : ~ active[i]

(* Safety: termination is only detected if all nodes are inactive. *)
TerminationDetection ==
  terminationDetected => AllInactive

(* Liveness: global termination is eventually detected. *)
Liveness ==
  AllInactive ~> terminationDetected

(* Property expected to fail: not every run terminates. *)
FalseLiveness ==
  []<>AllInactive

(* Stronger fairness assumption and an associated property. *)
SpecWFNext == Init /\ [][Next]_vars /\ WF_vars(Next)

AllNodesTerminateIfNoMessages ==
  <>[][\A i \in Node : ~ SendMsg(i)]_vars => <>AllInactive

-----------------------------------------------------------------------------
(***************************************************************************)
(* Dijkstra's inductive invariant.                                         *)
(***************************************************************************)
Inv ==
  \/ \A i \in Node : tpos < i => ~ active[i]
  \/ \E j \in 0 .. tpos : color[j] = "black"
  \/ tcolor = "black"

IndInv == TypeOK /\ Inv

THEOREM Spec => []TerminationDetection
THEOREM Spec => Liveness
=============================================================================