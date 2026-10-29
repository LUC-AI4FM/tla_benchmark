------------------------------- MODULE EWD840 -------------------------------
(***************************************************************************)
(* Dijkstra's EWD 840 termination detection algorithm on a ring of N nodes. *)
(* Node 0 initiates probes. The token travels from node i to node i-1.     *)
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

Init ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ color \in [Nodes -> Color]
  /\ tpos \in Nodes
  /\ tcolor = "black"

(***************************************************************************)
(* Node 0 initiates a new probe if the previous one was unsuccessful.      *)
(***************************************************************************)
InitiateProbe ==
  /\ tpos = 0
  /\ tcolor = "black" \/ color[0] = "black"
  /\ tpos' = N-1
  /\ tcolor' = "white"
  /\ active' = active
  /\ color' = [color EXCEPT ![0] = "white"]

(***************************************************************************)
(* Node i > 0 passes the token to node i-1 once it is inactive (or if the  *)
(* token or the node is already black).                                    *)
(***************************************************************************)
PassToken(i) ==
  /\ tpos = i
  /\ ~ active[i] \/ color[i] = "black" \/ tcolor = "black"
  /\ tpos' = i-1
  /\ tcolor' = IF color[i] = "black" THEN "black" ELSE tcolor
  /\ active' = active
  /\ color' = [color EXCEPT ![i] = "white"]

System == InitiateProbe \/ \E i \in Nodes \ {0} : PassToken(i)

(***************************************************************************)
(* Environment actions: sending messages and deactivation.                 *)
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
(* Properties.                                                             *)
(***************************************************************************)
NeverBlack == \A i \in Nodes : color[i] # "black"

NeverChangeColor == [][UNCHANGED color]_vars

terminationDetected ==
  /\ tpos = 0
  /\ tcolor = "white"
  /\ color[0] = "white"
  /\ ~ active[0]

TerminationDetection ==
  terminationDetected => \A i \in Nodes : ~ active[i]

Liveness ==
  (\A i \in Nodes : ~ active[i]) ~> terminationDetected

FalseLiveness ==
  (\A i \in Nodes : []<> ~ active[i]) ~> terminationDetected

SpecWFNext == Init /\ [][Next]_vars /\ WF_vars(Next)

AllNodesTerminateIfNoMessages ==
  <>[][\A i \in Nodes : ~ SendMsg(i)]_vars
     => <>(\A i \in Nodes : ~ active[i])

(***************************************************************************)
(* Dijkstra's inductive invariant.                                         *)
(***************************************************************************)
Inv ==
  \/ \A i \in Nodes : tpos < i => ~ active[i]
  \/ \E j \in 0 .. tpos : color[j] = "black"
  \/ tcolor = "black"

THEOREM Spec => []TypeOK
THEOREM Spec => []Inv
THEOREM Spec => []TerminationDetection
THEOREM Spec => Liveness
=============================================================================