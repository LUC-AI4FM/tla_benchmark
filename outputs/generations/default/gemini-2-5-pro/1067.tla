---------------- MODULE TerminationDetection ----------------

EXTENDS Naturals, FiniteSets

CONSTANTS Node

VARIABLES active, detected

vars == <<active, detected>>

TypeOK ==
    /\ active \in SUBSET Node
    /\ detected \in BOOLEAN

\* @type: () => BOOLEAN;
Init ==
    /\ active \in SUBSET Node
    /\ active /= {}
    /\ detected = FALSE

\* @type: (Node) => BOOLEAN;
Terminate(n) ==
    /\ n \in active
    /\ active' = active \ {n}
    /\ UNCHANGED detected

\* @type: (Node, Node) => BOOLEAN;
Wakeup(n, m) ==
    /\ n \in active
    /\ m \in Node \ active
    /\ active' = active \cup {m}
    /\ UNCHANGED detected

\* @type: () => BOOLEAN;
Detect ==
    /\ active = {}
    /\ \lnot detected
    /\ detected' = TRUE
    /\ UNCHANGED active

\* @type: () => BOOLEAN;
Next ==
    \/ \E n \in active : Terminate(n)
    \/ \E n \in active, m \in Node \ active : Wakeup(n, m)
    \/ Detect

\* The full specification, including weak fairness on the Detect action.
\* Weak fairness on Detect ensures that if the system becomes permanently
\* quiescent, termination is eventually detected.
\* @type: () => BOOLEAN;
Spec == Init /\ [][Next]_vars /\ WF_vars(Detect)

-----------------------------------------------------------------------------
\* PROPERTIES

\* Safety: If termination is detected, then all nodes must be inactive.
\* This is an invariant of the system.
Correctness == detected => (active = {})

\* Safety: If termination is detected, the system remains quiescent forever
\* (no node can become active again).
Quiescence == [] (detected => \box (active = {}))

\* Liveness: If the system eventually becomes permanently quiescent (all nodes
\* become and remain inactive), then termination is eventually detected.
Liveness == (<> \box (active = {})) ~> (<> detected)

=============================================================================