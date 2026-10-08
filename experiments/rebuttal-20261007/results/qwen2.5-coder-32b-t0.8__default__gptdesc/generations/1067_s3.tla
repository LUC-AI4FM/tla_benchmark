------------------------------- MODULE TerminationDetection -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Node

VARIABLES activeNodes, detected

Init == /\ activeNodes = Node
        /\ detected = FALSE

Next ==
    \/ /\ \/ EXIST node \in activeNodes : 
               \/ \/ activeNodes' = (activeNodes \ {node})
                  /\ detected' = detected
               \/ \/ EXISTS otherNode \in Node \ activeNodes :
                      activeNodes' = (activeNodes \ {node} \cup {otherNode})
                      /\ detected' = detected
          /\ detected' = detected
    \/ /\ detected' = TRUE
       /\ UNCHANGED activeNodes

Spec == SpecFairness /\ SpecProperties

SpecFairness ==
    WF_vars(Next, <<detected>>)

SpecProperties ==
    /\ Init \in StateSpace
    /\ []<>(/\ activeNodes = {} 
               /\ detected)
    /\ [](activeNodes = {} => <>[](detected))

StateSpace == {s \in [<<activeNodes, detected>> \-> S] :
                 /\ activeNodes' \subseteq Node
                 /\ detected' \in BOOLEAN}
=====================================================================================