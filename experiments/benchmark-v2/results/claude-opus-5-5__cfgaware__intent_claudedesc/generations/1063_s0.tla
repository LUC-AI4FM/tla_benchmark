---------------------------- MODULE EWD840Ring ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

Nodes == 0 .. N-1
Color == {"white", "black"}

\* Bound on messages queued at one node. It keeps the state space finite
\* for model checking.
MaxPending == 2

VARIABLES
    active,   \* active[i] : node i is currently active
    color,    \* color[i]  : color of node i
    tpos,     \* node currently holding the token
    tcolor,   \* color of the token
    pending   \* pending[i]: number of messages in transit to node i

vars == <<active, color, tpos, tcolor, pending>>

TypeOK ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ color \in [Nodes -> Color]
    /\ tpos \in Nodes
    /\ tcolor \in Color
    /\ pending \in [Nodes -> 0 .. MaxPending]

Init ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ color \in [Nodes -> Color]
    /\ tpos \in Nodes
    /\ tcolor = "black"
    /\ pending = [i \in Nodes |-> 0]

-----------------------------------------------------------------------------
(* Token handling *)

\* Node 0 starts a new probe when the previous one failed.
InitiateProbe ==
    /\ tpos = 0
    /\ tcolor = "black" \/ color[0] = "black"
    /\ tpos' = N - 1
    /\ tcolor' = "white"
    /\ color' = [color EXCEPT ![0] = "white"]
    /\ UNCHANGED <<active, pending>>

\* An inactive node with no queued messages passes the token to its
\* predecessor in the ring. A black node blackens the token and then
\* becomes white.
PassToken(i) ==
    /\ i # 0
    /\ tpos = i
    /\ ~active[i]
    /\ pending[i] = 0
    /\ tpos' = i - 1
    /\ tcolor' = IF color[i] = "black" THEN "black" ELSE tcolor
    /\ color' = [color EXCEPT ![i] = "white"]
    /\ UNCHANGED <<active, pending>>

-----------------------------------------------------------------------------
(* System actions *)

\* An active node sends a message to another node. The sender becomes
\* black, because the message may travel "behind" the token.
SendMsg(i) ==
    /\ active[i]
    /\ \E j \in Nodes \ {i} :
          /\ pending[j] < MaxPending
          /\ pending' = [pending EXCEPT ![j] = @ + 1]
    /\ color' = [color EXCEPT ![i] = "black"]
    /\ UNCHANGED <<active, tpos, tcolor>>

\* A node receives a message and becomes (re)activated.
RecvMsg(i) ==
    /\ pending[i] > 0
    /\ pending' = [pending EXCEPT ![i] = @ - 1]
    /\ active' = [active EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<color, tpos, tcolor>>

\* An active node becomes inactive.
Deactivate(i) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<color, tpos, tcolor, pending>>

-----------------------------------------------------------------------------

System ==
    \/ InitiateProbe
    \/ \E i \in Nodes \ {0} : PassToken(i)

Environment ==
    \E i \in Nodes : SendMsg(i) \/ RecvMsg(i) \/ Deactivate(i)

Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------
(* Correctness *)

\* The system has actually terminated.
Terminated ==
    /\ \A i \in Nodes : ~active[i]
    /\ \A i \in Nodes : pending[i] = 0

\* The detector declares termination.
TerminationDetected ==
    /\ tpos = 0
    /\ tcolor = "white"
    /\ color[0] = "white"
    /\ ~active[0]
    /\ pending[0] = 0

\* Safety: detected termination implies actual termination.
TerminationDetectionSafe == TerminationDetected => Terminated

\* Liveness: actual termination is eventually detected.
Liveness == Terminated ~> TerminationDetected

JsonInv ==
    /\ TypeOK
    /\ TerminationDetectionSafe

=============================================================================