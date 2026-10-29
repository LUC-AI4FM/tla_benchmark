------------------------------- MODULE EWD840 -------------------------------
(***************************************************************************)
(* Dijkstra's ring termination-detection algorithm (EWD 840), extended     *)
(* with asynchronous message delivery. N processes form a ring, and the    *)
(* token travels from node i to node i-1. Node 0 is the leader.            *)
(*                                                                         *)
(* Sending a message puts it "in flight" (pending at the destination).     *)
(* Delivering it later activates the destination. A process that sends a  *)
(* message to a higher-indexed process colors itself black. A process may  *)
(* pass the token in the neutral (white) way only when it is passive and   *)
(* has no undelivered incoming messages.                                   *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

VARIABLES active, color, tokenPos, tcolor, pending

Nodes      == 0 .. N-1
Color      == {"white", "black"}
MaxPending == 2   \* bound on in-flight messages per destination (finite model)

vars == <<active, color, tokenPos, tcolor, pending>>

TypeOK ==
  /\ active   \in [Nodes -> BOOLEAN]
  /\ color    \in [Nodes -> Color]
  /\ tokenPos \in Nodes
  /\ tcolor   \in Color
  /\ pending  \in [Nodes -> 0 .. MaxPending]

-----------------------------------------------------------------------------
Init ==
  /\ active   \in [Nodes -> BOOLEAN]
  /\ color    \in [Nodes -> Color]
  /\ tokenPos \in Nodes
  /\ tcolor   = "black"
  /\ pending  = [i \in Nodes |-> 0]

(* The leader starts a new probe when it holds the token and the previous *)
(* round was inconclusive (black token or black leader).                  *)
InitiateProbe ==
  /\ tokenPos = 0
  /\ \/ tcolor = "black"
     \/ color[0] = "black"
  /\ tokenPos' = N-1
  /\ tcolor'   = "white"
  /\ color'    = [color EXCEPT ![0] = "white"]
  /\ UNCHANGED <<active, pending>>

(* Node i > 0 passes the token to node i-1. The token turns black if node i *)
(* is black, and node i turns white again.                                 *)
PassToken(i) ==
  /\ tokenPos = i
  /\ \/ (~active[i] /\ pending[i] = 0)
     \/ color[i] = "black"
     \/ tcolor = "black"
  /\ tokenPos' = i-1
  /\ tcolor'   = IF color[i] = "black" THEN "black" ELSE tcolor
  /\ color'    = [color EXCEPT ![i] = "white"]
  /\ UNCHANGED <<active, pending>>

System == InitiateProbe \/ \E i \in Nodes \ {0} : PassToken(i)

(* An active node sends a message asynchronously to another node. Sending  *)
(* to a higher-indexed node marks potential forward activity (black).      *)
SendMsg(i) ==
  /\ active[i]
  /\ \E j \in Nodes \ {i} :
       /\ pending[j] < MaxPending
       /\ pending' = [pending EXCEPT ![j] = @ + 1]
       /\ color'   = IF j > i THEN [color EXCEPT ![i] = "black"] ELSE color
  /\ UNCHANGED <<active, tokenPos, tcolor>>

(* Delivery of an in-flight message activates the receiver. *)
Deliver(i) ==
  /\ pending[i] > 0
  /\ pending' = [pending EXCEPT ![i] = @ - 1]
  /\ active'  = [active EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<color, tokenPos, tcolor>>

(* An active node finishes its local computation. *)
Deactivate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<color, tokenPos, tcolor, pending>>

Environment == \E i \in Nodes : SendMsg(i) \/ Deliver(i) \/ Deactivate(i)

Next == System \/ Environment

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(System)
  /\ \A i \in Nodes : WF_vars(Deliver(i))

-----------------------------------------------------------------------------
(* A node is busy if it is active or has undelivered incoming messages. *)
busy == [i \in Nodes |-> active[i] \/ pending[i] > 0]

terminated == \A i \in Nodes : ~active[i] /\ pending[i] = 0

terminationDetected ==
  /\ tokenPos = 0
  /\ tcolor = "white"
  /\ color[0] = "white"
  /\ ~active[0]
  /\ pending[0] = 0

(* Safety: detection is sound. *)
TerminationDetection ==
  terminationDetected => \A i \in Nodes : ~active[i]

(* Liveness: once the system has terminated, termination is detected. *)
Liveness == terminated ~> terminationDetected

(* Inductive invariant (EWD 840). *)
Inv ==
  \/ \A i \in Nodes : tokenPos < i => (~active[i] /\ pending[i] = 0)
  \/ \E j \in 0 .. tokenPos : color[j] = "black"
  \/ tcolor = "black"

-----------------------------------------------------------------------------
(* Abstract termination-detection specification, refined by Spec. *)
tdvars == <<busy, terminationDetected>>

TDInit ==
  /\ busy \in [Nodes -> BOOLEAN]
  /\ terminationDetected \in {FALSE, terminated}

TDNext ==
  \/ /\ ~terminated
     /\ busy' \in [Nodes -> BOOLEAN]
     /\ terminationDetected' \in {FALSE, terminated'}
  \/ /\ terminated
     /\ ~terminationDetected
     /\ terminationDetected' = TRUE
     /\ busy' = busy

TDSpec ==
  /\ TDInit
  /\ [][TDNext]_tdvars
  /\ (terminated ~> terminationDetected)

THEOREM Spec => []TypeOK
THEOREM Spec => []Inv
THEOREM Spec => []TerminationDetection
THEOREM Spec => Liveness
THEOREM Spec => TDSpec
=============================================================================