----------------------------- MODULE TerminationRing -----------------------------

EXTENDS Naturals

CONSTANTS 
    Node,           \* Nonempty set of nodes arranged in a ring
    Succ            \* Successor function: Node -> Node (next node on the ring)

ASSUME /\ Node # {}
       /\ Succ \in [Node -> Node]
       /\ \A n \in Node : Succ[n] \in Node

VARIABLES 
    active,         \* Function: Node -> BOOLEAN, whether each node is active
    detected        \* BOOLEAN flag indicating whether global termination was detected

vars == << active, detected >>

TypeOK == /\ active \in [Node -> BOOLEAN]
          /\ detected \in BOOLEAN

ActiveNodes == { n \in Node : active[n] }
AllInactive == \A n \in Node : ~active[n]

Init == /\ TypeOK
        /\ detected = FALSE
        /\ active \in [Node -> BOOLEAN]    \* Arbitrary initial activity

Terminate(i) == 
    /\ i \in Node
    /\ ~detected
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED detected

Wake(i) ==
    /\ i \in Node
    /\ ~detected
    /\ active[i]
    /\ LET j == Succ[i]
       IN active' = [active EXCEPT ![j] = TRUE]
    /\ UNCHANGED detected

Detect ==
    /\ ~detected
    /\ AllInactive
    /\ detected' = TRUE
    /\ UNCHANGED active

Next ==
    \/ (\E i \in Node : Terminate(i))
    \/ (\E i \in Node : Wake(i))
    \/ Detect

Spec == Init /\ [][Next]_vars /\ WF_vars(Detect)

\* Safety invariants
SafetyTypeInv == []TypeOK
NoFalseDetection == [](detected => AllInactive)
DetectionStable == [](detected => [] detected)

\* Quiescence: once detection occurs, the set of active nodes never changes thereafter
Quiescence == [](detected => [] (active' = active))

\* Liveness-style property: if the system becomes permanently inactive,
\* then detection eventually occurs (guaranteed by weak fairness of Detect)
EventualDetectionUnderStability == (<>[] AllInactive) => (<> detected)

=============================================================================