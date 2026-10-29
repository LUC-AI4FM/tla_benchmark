------------------------------- MODULE APAEWD840 -------------------------------
(***************************************************************************)
(* Apalache type annotations for EWD840, Dijkstra's token ring algorithm   *)
(* for detecting termination in a distributed system.  The EWD840          *)
(* definitions are inlined so that this module is self-contained.          *)
(* Model-checking configuration: N = 3, INVARIANTS TypeOK and              *)
(* TerminationDetection, deadlock checking disabled.                       *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT
    \* @type: Int;
    N

ASSUME NAssumption == N \in Nat \ {0}

VARIABLES
    \* @type: Int -> Bool;
    active,
    \* @type: Int -> Str;
    color,
    \* @type: Int;
    tpos,
    \* @type: Str;
    tcolor

vars == <<active, color, tpos, tcolor>>

\* Apalache constant initialization: three nodes in the ring
ConstInit == N = 3

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

\* Node 0 initiates a new probe when it holds the token and the previous
\* round was unsuccessful.
InitiateProbe ==
    /\ tpos = 0
    /\ tcolor = "black" \/ color[0] = "black"
    /\ tpos' = N - 1
    /\ tcolor' = "white"
    /\ active' = active
    /\ color' = [color EXCEPT ![0] = "white"]

\* Node i > 0 passes the token to node i-1.
PassToken(i) ==
    /\ tpos = i
    /\ i # 0
    /\ ~active[i] \/ color[i] = "black" \/ tcolor = "black"
    /\ tpos' = i - 1
    /\ tcolor' = IF color[i] = "black" THEN "black" ELSE tcolor
    /\ active' = active
    /\ color' = [color EXCEPT ![i] = "white"]

System == InitiateProbe \/ \E i \in Nodes \ {0} : PassToken(i)

\* An active node i sends a message to node j, activating it.
SendMsg(i) ==
    /\ active[i]
    /\ \E j \in Nodes \ {i} :
          /\ active' = [active EXCEPT ![j] = TRUE]
          /\ color' = [color EXCEPT ![i] = IF j > i THEN "black" ELSE @]
    /\ UNCHANGED <<tpos, tcolor>>

\* An active node becomes inactive.
Deactivate(i) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<color, tpos, tcolor>>

Environment == \E i \in Nodes : SendMsg(i) \/ Deactivate(i)

Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------
\* All nodes are inactive (no pending messages are modeled explicitly).
terminated == \A i \in Nodes : ~active[i]

\* The algorithm reports termination.
terminationDetected ==
    /\ tpos = 0
    /\ tcolor = "white"
    /\ color[0] = "white"
    /\ ~active[0]

\* Safety: if termination is detected, all nodes are indeed inactive.
TerminationDetection == terminationDetected => terminated

\* Liveness: once the system has terminated, termination is eventually detected.
Liveness == terminated ~> terminationDetected

THEOREM Spec => [](TypeOK /\ TerminationDetection)
=============================================================================