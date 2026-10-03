---- MODULE TerminationDetection ----
EXTENDS Naturals, FiniteSets

CONSTANT Node
ASSUME IsFiniteSet(Node) /\ Node # {}

VARIABLES active, detected

vars == <<active, detected>>

\* The set of active nodes is a subset of all nodes.
\* The detected flag is a boolean.
TypeOK == /\ active \subseteq Node
          /\ detected \in BOOLEAN

\* Initially, all nodes are active and termination has not been detected.
Init == /\ active = Node
        /\ detected = FALSE

\* An active node i becomes inactive.
Terminate(i) == /\ i \in active
                /\ active' = active \ {i}
                /\ UNCHANGED detected

\* An active node i wakes up node j, making it active.
Wakeup(i, j) == /\ i \in active
                /\ j \in Node
                /\ active' = active \cup {j}
                /\ UNCHANGED detected

\* If all nodes are inactive and termination has not been detected,
\* the detected flag is set.
Detect == /\ active = {}
          /\ \lnot detected
          /\ detected' = TRUE
          /\ UNCHANGED active

\* The next-state relation combines all possible actions.
Next == \/ \E i \in Node : Terminate(i)
        \/ \E i, j \in Node : Wakeup(i, j)
        \/ Detect

\* The main specification, stating initial conditions, the next-state
\* relation, and a weak fairness condition on the Detect action.
Spec == Init /\ [][Next]_vars /\ WF_vars(Detect)

\* Correctness Invariant: If termination is detected, then all nodes are inactive.
Correctness == detected => (active = {})

\* Quiescence Property: If the system is quiescent (all nodes inactive)
\* and termination has not been detected, the Detect action must be enabled.
Quiescence == (active = {} /\ \lnot detected) => ENABLED Detect

\* Liveness Property: Eventually, termination is detected.
Liveness == <>detected

=============================================================================