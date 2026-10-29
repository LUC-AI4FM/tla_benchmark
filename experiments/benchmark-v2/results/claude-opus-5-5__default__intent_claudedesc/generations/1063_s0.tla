------------------------------- MODULE EWD840 -------------------------------
(***************************************************************************)
(* Dijkstra's EWD840 termination detection algorithm on a ring of N nodes, *)
(* extended with explicit in-flight messages (a per-node count of pending  *)
(* messages).                                                              *)
(*                                                                         *)
(* The token travels from node 0 to N-1, then N-2, and so on down to 0.    *)
(* Node 0 detects termination when it holds a white token, is white,       *)
(* inactive, and has no pending messages.                                  *)
(*                                                                         *)
(* A node that sends a message turns black. A node may pass the token      *)
(* while white only if it is inactive and has no undelivered messages      *)
(* addressed to it. Otherwise the token is tainted (black), so that round  *)
(* fails.                                                                  *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

Node  == 0 .. N-1
Color == {"white", "black"}

VARIABLES
    active,   \* active[i] : is node i currently active?
    color,    \* color[i]  : color of node i
    pending,  \* pending[i]: number of messages in transit to node i
    tpos,     \* index of the node currently holding the token
    tcolor    \* color of the token

vars == << active, color, pending, tpos, tcolor >>

TypeOK ==
    /\ active  \in [Node -> BOOLEAN]
    /\ color   \in [Node -> Color]
    /\ pending \in [Node -> Nat]
    /\ tpos    \in Node
    /\ tcolor  \in Color

-----------------------------------------------------------------------------
Init ==
    /\ active  \in [Node -> BOOLEAN]
    /\ color   \in [Node -> Color]
    /\ pending = [i \in Node |-> 0]
    /\ tpos    \in Node
    /\ tcolor  = "black"

(***************************************************************************)
(* Node 0 starts a new probe when the previous round failed.               *)
(***************************************************************************)
InitiateProbe ==
    /\ tpos = 0
    /\ tcolor = "black" \/ color[0] = "black"
    /\ tpos'   = N-1
    /\ tcolor' = "white"
    /\ color'  = [color EXCEPT ![0] = "white"]
    /\ UNCHANGED << active, pending >>

(***************************************************************************)
(* Node i > 0 passes the token to node i-1. A white node with an untainted *)
(* token may only pass it when it is quiescent: inactive and with no       *)
(* pending messages. A black node, or a black token, may always be         *)
(* passed, because that round is already doomed. The node whitens itself.  *)
(***************************************************************************)
PassToken(i) ==
    /\ tpos = i
    /\ i # 0
    /\ \/ (~active[i] /\ pending[i] = 0)
       \/ color[i] = "black"
       \/ tcolor = "black"
    /\ tpos'   = i - 1
    /\ tcolor' = IF color[i] = "black" THEN "black" ELSE tcolor
    /\ color'  = [color EXCEPT ![i] = "white"]
    /\ UNCHANGED << active, pending >>

System == InitiateProbe \/ \E i \in Node \ {0} : PassToken(i)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Environment (underlying computation).                                   *)
(***************************************************************************)

\* An active node sends a message to another node and turns black.
SendMsg(i) ==
    /\ active[i]
    /\ \E j \in Node \ {i} :
          pending' = [pending EXCEPT ![j] = @ + 1]
    /\ color' = [color EXCEPT ![i] = "black"]
    /\ UNCHANGED << active, tpos, tcolor >>

\* Receiving a message (re)activates the node.
RecvMsg(i) ==
    /\ pending[i] > 0
    /\ pending' = [pending EXCEPT ![i] = @ - 1]
    /\ active'  = [active EXCEPT ![i] = TRUE]
    /\ UNCHANGED << color, tpos, tcolor >>

\* An active node spontaneously becomes inactive.
Deactivate(i) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED << color, pending, tpos, tcolor >>

Environment ==
    \E i \in Node : SendMsg(i) \/ RecvMsg(i) \/ Deactivate(i)

-----------------------------------------------------------------------------
Next == System \/ Environment

\* Fairness applies only to the detection algorithm, not to the computation.
Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Correctness properties                                                  *)
(***************************************************************************)

\* Actual global termination: all nodes inactive, no messages in transit.
Terminated ==
    /\ \A i \in Node : ~active[i]
    /\ \A i \in Node : pending[i] = 0

\* Node 0 claims termination.
terminationDetected ==
    /\ tpos = 0
    /\ tcolor = "white"
    /\ color[0] = "white"
    /\ ~active[0]
    /\ pending[0] = 0

\* Main safety invariant: detection implies actual termination.
TerminationDetection ==
    terminationDetected => Terminated

\* No false positives: never claim termination while work remains.
NoFalsePositives ==
    ~( terminationDetected
       /\ (\/ \E i \in Node : active[i]
           \/ \E i \in Node : pending[i] > 0) )

\* Once terminated, the system stays terminated.
TerminatedStable == [](Terminated => []Terminated)

\* Liveness: if the system terminates, termination is eventually detected.
Liveness == Terminated ~> terminationDetected

\* Optional state constraint to bound the state space for model checking.
CONSTANT MaxPending
StateConstraint == \A i \in Node : pending[i] <= MaxPending

THEOREM Spec => []TypeOK
THEOREM Spec => []TerminationDetection
THEOREM Spec => []NoFalsePositives
THEOREM Spec => Liveness
=============================================================================