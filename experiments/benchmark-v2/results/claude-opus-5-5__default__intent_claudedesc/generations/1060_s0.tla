------------------------------- MODULE EWD840 -------------------------------
(***************************************************************************)
(* Dijkstra's token ring termination detection algorithm (EWD 840).        *)
(* N processes, numbered 0..N-1, are arranged in a ring. Node 0 is the     *)
(* initiator. The token travels from node i to node i-1, and node 0 sends  *)
(* it to node N-1. Message transmission is modeled as atomic, so a message *)
(* activates its receiver immediately and no message is ever in transit.   *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

VARIABLES active, color, tpos, tcolor

vars == <<active, color, tpos, tcolor>>

Node  == 0 .. N-1
Color == {"white", "black"}

TypeOK ==
  /\ active \in [Node -> BOOLEAN]
  /\ color  \in [Node -> Color]
  /\ tpos   \in Node
  /\ tcolor \in Color

(***************************************************************************)
(* Initially the processes have arbitrary activity and colors. The token   *)
(* is at an arbitrary node and is black, so the first probe cannot falsely *)
(* announce termination.                                                    *)
(***************************************************************************)
Init ==
  /\ active \in [Node -> BOOLEAN]
  /\ color  \in [Node -> Color]
  /\ tpos   \in Node
  /\ tcolor = "black"

(***************************************************************************)
(* Node 0 starts a new probe when the previous one was unsuccessful. It    *)
(* sends a white token to node N-1 and makes itself white.                 *)
(***************************************************************************)
InitiateProbe ==
  /\ tpos = 0
  /\ tcolor = "black" \/ color[0] = "black"
  /\ tpos' = N-1
  /\ tcolor' = "white"
  /\ color' = [color EXCEPT ![0] = "white"]
  /\ UNCHANGED active

(***************************************************************************)
(* Node i > 0 passes the token to node i-1 once it is inactive. If it is   *)
(* black, or the token is already black, it may pass the token at once,    *)
(* because the probe has already failed. A black node blackens the token.  *)
(* After passing the token, the node becomes white.                        *)
(***************************************************************************)
PassToken(i) ==
  /\ tpos = i
  /\ ~ active[i] \/ color[i] = "black" \/ tcolor = "black"
  /\ tpos' = i-1
  /\ tcolor' = IF color[i] = "black" THEN "black" ELSE tcolor
  /\ color' = [color EXCEPT ![i] = "white"]
  /\ UNCHANGED active

(***************************************************************************)
(* These are the actions of the token-passing algorithm.                   *)
(***************************************************************************)
System == InitiateProbe \/ \E i \in Node \ {0} : PassToken(i)

(***************************************************************************)
(* An active node i sends a message to another node j. Node j becomes      *)
(* active. If j > i, the message goes "backward" relative to the token,    *)
(* which travels downward. In that case node i turns black.                *)
(***************************************************************************)
SendMsg(i) ==
  /\ active[i]
  /\ \E j \in Node \ {i} :
        /\ active' = [active EXCEPT ![j] = TRUE]
        /\ color'  = [color EXCEPT ![i] = IF j > i THEN "black" ELSE @]
  /\ UNCHANGED <<tpos, tcolor>>

(***************************************************************************)
(* An active node may become inactive at any time.                         *)
(***************************************************************************)
Deactivate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<color, tpos, tcolor>>

(***************************************************************************)
(* These are the actions of the underlying distributed computation.        *)
(***************************************************************************)
Environment == \E i \in Node : SendMsg(i) \/ Deactivate(i)

Next == System \/ Environment

(***************************************************************************)
(* Weak fairness on the detection algorithm. No fairness is assumed for    *)
(* the underlying computation.                                              *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Termination is the state in which all processes are inactive. Messages  *)
(* are atomic, so no message can be in transit.                            *)
(***************************************************************************)
Terminated == \A i \in Node : ~ active[i]

(***************************************************************************)
(* Node 0 detects termination when it holds a white token, is white        *)
(* itself, and is inactive.                                                 *)
(***************************************************************************)
terminationDetected ==
  /\ tpos = 0
  /\ tcolor = "white"
  /\ color[0] = "white"
  /\ ~ active[0]

(***************************************************************************)
(* Safety: termination is announced only if all nodes are inactive.        *)
(***************************************************************************)
TerminationDetection == terminationDetected => Terminated

(***************************************************************************)
(* Liveness: once the system has terminated, termination is eventually     *)
(* detected.                                                                *)
(***************************************************************************)
Liveness == Terminated ~> terminationDetected

(***************************************************************************)
(* Inductive invariant from Dijkstra's proof. At least one of the          *)
(* following holds:                                                         *)
(* - every node the token has already visited is inactive;                 *)
(* - some node not yet visited is black;                                   *)
(* - the token is black.                                                   *)
(***************************************************************************)
Inv ==
  \/ \A i \in Node : tpos < i => ~ active[i]
  \/ \E j \in 0 .. tpos : color[j] = "black"
  \/ tcolor = "black"

(***************************************************************************)
(* Once terminated, the system stays terminated.                           *)
(***************************************************************************)
TerminationStable == [](Terminated => []Terminated)

THEOREM Spec => []TypeOK
THEOREM Spec => []Inv
THEOREM Spec => []TerminationDetection
THEOREM Spec => Liveness
=============================================================================