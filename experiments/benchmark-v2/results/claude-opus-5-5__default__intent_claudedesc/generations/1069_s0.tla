---------------------------- MODULE AsyncTerminationDetection ----------------------------
EXTENDS Naturals

CONSTANTS N,            \* number of nodes in the ring
          MaxPending    \* bound on pending messages per node (for model checking)

ASSUME NAssumption == N \in Nat \ {0}
ASSUME MaxPendingAssumption == MaxPending \in Nat \ {0}

Node == 0 .. N-1

VARIABLES
    active,               \* active[n] : is node n active?
    pending,              \* pending[n] : number of messages pending at node n
    terminationDetected   \* has termination been detected?

vars == << active, pending, terminationDetected >>

-----------------------------------------------------------------------------------------
TypeOK ==
    /\ active \in [Node -> BOOLEAN]
    /\ pending \in [Node -> 0 .. MaxPending]
    /\ terminationDetected \in BOOLEAN

\* True termination: all nodes inactive and no pending messages.
terminated == \A n \in Node : ~active[n] /\ pending[n] = 0

-----------------------------------------------------------------------------------------
Init ==
    /\ active \in [Node -> BOOLEAN]
    /\ pending = [n \in Node |-> 0]
    /\ terminationDetected \in {FALSE, terminated}

\* An active node voluntarily becomes inactive. Detection may optionally
\* happen at the same moment if this step terminates the system.
Terminate(i) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ pending' = pending
    /\ terminationDetected' \in {terminationDetected, terminated'}

\* An active node i sends a message to node j.
SendMsg(i, j) ==
    /\ active[i]
    /\ pending[j] < MaxPending
    /\ pending' = [pending EXCEPT ![j] = @ + 1]
    /\ UNCHANGED << active, terminationDetected >>

\* Node i receives a pending message and becomes active.
Wakeup(i) ==
    /\ pending[i] > 0
    /\ active' = [active EXCEPT ![i] = TRUE]
    /\ pending' = [pending EXCEPT ![i] = @ - 1]
    /\ UNCHANGED terminationDetected

\* Termination is detected.
DetectTermination ==
    /\ terminated
    /\ ~terminationDetected
    /\ terminationDetected' = TRUE
    /\ UNCHANGED << active, pending >>

Next ==
    \/ \E i \in Node : Terminate(i)
    \/ \E i, j \in Node : SendMsg(i, j)
    \/ \E i \in Node : Wakeup(i)
    \/ DetectTermination

Spec == Init /\ [][Next]_vars /\ WF_vars(DetectTermination)

-----------------------------------------------------------------------------------------
\* Safety: the detection flag never lies.
TerminationDetectionSafe == terminationDetected => terminated

\* Quiescence: once terminated, the system remains terminated.
Quiescence == [][terminated => terminated']_vars

\* Liveness: actual termination is eventually detected.
TerminationDetectionLive == terminated ~> terminationDetected

THEOREM Spec => []TypeOK
THEOREM Spec => []TerminationDetectionSafe
THEOREM Spec => Quiescence
THEOREM Spec => TerminationDetectionLive
=========================================================================================