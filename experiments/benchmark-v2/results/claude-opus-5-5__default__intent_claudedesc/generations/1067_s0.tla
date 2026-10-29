---------------------------- MODULE SyncTerminationDetection ----------------------------
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

Node == 0 .. N-1

VARIABLES
    active,               \* active[n] = TRUE iff node n is active
    terminationDetected   \* TRUE iff termination has been reported

vars == <<active, terminationDetected>>

terminated == \A n \in Node : ~ active[n]

-----------------------------------------------------------------------------------------

TypeOK ==
    /\ active \in [Node -> BOOLEAN]
    /\ terminationDetected \in BOOLEAN

Init ==
    /\ active \in [Node -> BOOLEAN]
    /\ terminationDetected \in {FALSE, terminated}

\* A node spontaneously becomes inactive.
Terminate(i) ==
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED terminationDetected

\* An active node i wakes up node j (synchronous communication).
Wakeup(i, j) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![j] = TRUE]
    /\ UNCHANGED terminationDetected

\* Detection of termination once all nodes are inactive.
DetectTermination ==
    /\ terminated
    /\ ~ terminationDetected
    /\ terminationDetected' = TRUE
    /\ UNCHANGED active

Next ==
    \/ \E i \in Node : Terminate(i)
    \/ \E i, j \in Node : Wakeup(i, j)
    \/ DetectTermination

Spec == Init /\ [][Next]_vars /\ WF_vars(DetectTermination)

-----------------------------------------------------------------------------------------
\* Correctness properties

\* Safety: termination is never falsely reported.
TDCorrect == terminationDetected => terminated

\* Termination is stable: once all nodes are inactive, they remain so forever.
Stable == [](terminated => []terminated)

\* Liveness: whenever all nodes are inactive, termination is eventually detected.
Live == terminated ~> terminationDetected

THEOREM Spec => [](TypeOK /\ TDCorrect)
THEOREM Spec => Stable
THEOREM Spec => Live
=========================================================================================