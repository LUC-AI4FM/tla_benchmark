------------------------- MODULE SyncTerminationDetection -------------------------
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

Node == 0 .. N-1

VARIABLES
    active,               \* active[n] = TRUE iff node n is active
    terminationDetected   \* TRUE iff termination has been declared

vars == <<active, terminationDetected>>

TypeOK ==
    /\ active \in [Node -> BOOLEAN]
    /\ terminationDetected \in BOOLEAN

\* Global termination: all nodes are inactive
terminated == \A n \in Node : ~active[n]

-----------------------------------------------------------------------------

Init ==
    /\ active \in [Node -> BOOLEAN]
    /\ terminationDetected \in {FALSE, terminated}

\* An active node becomes inactive on its own.
\* Detection may optionally happen synchronously at the same step.
Terminate(i) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ terminationDetected' \in {terminationDetected, terminated'}

\* An active node i activates a currently inactive node j.
Wakeup(i, j) ==
    /\ active[i]
    /\ ~active[j]
    /\ active' = [active EXCEPT ![j] = TRUE]
    /\ UNCHANGED terminationDetected

\* Synchronous (global) check: all nodes are inspected at once.
DetectTermination ==
    /\ terminated
    /\ ~terminationDetected
    /\ terminationDetected' = TRUE
    /\ UNCHANGED active

Next ==
    \/ \E i \in Node : Terminate(i)
    \/ \E i, j \in Node : Wakeup(i, j)
    \/ DetectTermination

Spec == Init /\ [][Next]_vars /\ WF_vars(DetectTermination)

-----------------------------------------------------------------------------

\* Safety: no false positives
TDCorrect == terminationDetected => terminated

\* Termination is stable: once all nodes are inactive they stay inactive
StableTermination == [](terminated => []terminated)

\* Detection is stable once declared
StableDetection == [](terminationDetected => []terminationDetected)

\* Liveness: if the system terminates, termination is eventually detected
Liveness == terminated ~> terminationDetected

\* Alternative formulation: if eventually always terminated, eventually detected
EventualDetection == (<>[]terminated) => <>terminationDetected

THEOREM Spec => [](TypeOK /\ TDCorrect)
THEOREM Spec => Liveness
=============================================================================