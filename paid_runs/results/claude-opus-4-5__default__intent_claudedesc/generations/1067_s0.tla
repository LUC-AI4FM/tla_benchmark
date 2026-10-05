---------------------------- MODULE TerminationDetection ----------------------------

EXTENDS Integers, FiniteSets

CONSTANTS N

ASSUME N \in Nat /\ N > 0

VARIABLES
    active,           \* active[i] = TRUE iff node i is active
    terminationDetected  \* TRUE iff termination has been detected

vars == <<active, terminationDetected>>

Nodes == 0..(N-1)

\* All nodes are inactive
AllInactive == \A i \in Nodes : ~active[i]

\* Initial state: any combination of active/inactive, detection may be true if all inactive
Init ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ terminationDetected \in {FALSE, AllInactive}

\* An active node spontaneously deactivates
Deactivate(i) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED terminationDetected

\* An active node wakes up another node
WakeUp(i, j) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![j] = TRUE]
    /\ UNCHANGED terminationDetected

\* Detection action: when all nodes are inactive, set the detected flag
Detect ==
    /\ AllInactive
    /\ ~terminationDetected
    /\ terminationDetected' = TRUE
    /\ UNCHANGED active

\* Next state relation
Next ==
    \/ \E i \in Nodes : Deactivate(i)
    \/ \E i, j \in Nodes : WakeUp(i, j)
    \/ Detect

\* Specification with weak fairness on detection
Spec == Init /\ [][Next]_vars /\ WF_vars(Detect)

\* ----- Safety Invariants -----

\* Safety: termination is never falsely reported
\* The detected flag may only be true when all nodes are genuinely inactive
SafetyNoFalseDetection == terminationDetected => AllInactive

\* ----- Stability Property -----

\* Stability: once all nodes are inactive, they remain so forever
\* This is expressed as: if all inactive now, then all inactive in the next state
StabilityInvariant == AllInactive => [][AllInactive]_vars

\* ----- Liveness Property -----

\* Liveness: whenever all nodes are inactive, termination is eventually detected
LivenessDetection == AllInactive ~> terminationDetected

\* ----- Combined Properties -----

\* Type invariant for state space
TypeOK ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ terminationDetected \in BOOLEAN

=============================================================================