------------------------------- MODULE TerminationDetection -------------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Node

VARIABLES activeNodes, detected

Init == /\ activeNodes \in SUBSET Node
        /\ detected = FALSE

Next ==
    \/ /\ ELEM(node \in activeNodes) 
       /\ 'activeNodes' = (activeNodes \ {node})
    \/ /\ ELEM(node \in activeNodes)
       /\ otherNode \in Node \ {node}
       /\ ~ otherNode \in activeNodes
       /\ 'activeNodes' = (activeNodes \ {node} \cup {otherNode})
    \/ /\ detected = FALSE
       /\ activeNodes = {}
       /\ 'detected' = TRUE

Spec == /\ Init
        /\ [][Next]_<<activeNodes, detected>>
        /\ WF_[Next]_<<>>

\* Safety invariants
Inv1 == detected => (activeNodes = {})

\* Liveness properties
Live1 == <>(/\ activeNodes = {}
            /\ detected = TRUE)

Correctness == Spec /\ []Inv1 /\ Live1

Quiescence ==
    /\ []<>(/\ activeNodes = {}
             /\ detected = TRUE)
    /\ [](detected => (activeNodes = {}))

Liveness ==
    \/ Quiescence

=============================================================================