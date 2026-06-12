---- MODULE DijkstraScholtenRing ----

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Nodes, Initiator \* Set of node identifiers and the distinguished initiator

VARIABLES tokenHolder, colors, deficits, vectorClocks, payloads

Init == /\ tokenHolder = Initiator
        /\ colors = [n \in Nodes |-> "white"]
        /\ deficits = [n \in Nodes |-> 0]
        /\ vectorClocks = [n \in Nodes |-> <<>>]
        /\ payloads = [n \in Nodes |-> {}]

Next == \/ TokenPassing
        \/ EnvironmentActions

TokenPassing ==
    LET nextHolder == IF tokenHolder = Initiator THEN CHOOSE n \in Nodes : n # Initiator ELSE CHOOSE n \in Nodes : n # tokenHolder
    IN /\ colors[tokenHolder] = "white"
       /\ deficits[tokenHolder] = 0
       /\ vectorClocks' = [vc EXCEPT ![tokenHolder] = Append(vectorClocks[tokenHolder], <<tokenHolder>>)]
       /\ colors' = [c EXCEPT ![nextHolder] = IF colors[nextHolder] = "black" THEN "white" ELSE c]
       /\ deficits' = [d EXCEPT ![nextHolder] = d[nextHolder] + (IF colors[nextHolder] = "black" THEN 1 ELSE 0)]
       /\ tokenHolder' = nextHolder
       /\ UNCHANGED <<payloads>>

EnvironmentActions ==
    \/ /\ \E n \in Nodes : colors[n] = "white"
       /\ /\ payloads' = [p EXCEPT ![n] = p[n] \cup {<<m, msg>>}]
          /\ vectorClocks' = [vc EXCEPT ![n] = Append(vectorClocks[n], <<n>>)]
          /\ UNCHANGED <<tokenHolder, colors, deficits>>
    \/ /\ \E n \in Nodes : colors[n] = "black"
       /\ /\ payloads' = [p EXCEPT ![n] = p[n] \ {<<m, msg>>}]
          /\ vectorClocks' = [vc EXCEPT ![n] = Append(vectorClocks[n], <<n>>)]
          /\ UNCHANGED <<tokenHolder, colors, deficits>>

Spec ==
    /\ Init
    /\ [][Next]_<<tokenHolder, colors, deficits, vectorClocks, payloads>>
    /\ WFTokenSystem

WFTokenSystem == WF_[<<TokenPassing>>]_<<tokenHolder, colors, deficits, vectorClocks, payloads>>

TerminationDetected ==
    /\ tokenHolder = Initiator
    /\ colors[Initiator] = "white"
    /\ deficits[Initiator] = 0

BoundedRoundProperty ==
    <>(TerminationDetected) ~> [](<>TerminationDetected)

RefinementMapping ==
    /\ \A n \in Nodes : colors'[n] = EWD998Chan!colors'[n]
    /\ \A n \in Nodes : deficits'[n] = EWD998Chan!deficits'[n]
    /\ \A n \in Nodes : vectorClocks'[n] = EWD998Chan!vectorClocks'[n]

SafetyRefinement ==
    Spec => EWD998Chan!Spec

LivenessRefinement ==
    BoundedRoundProperty => EWD998Chan!BoundedRoundProperty
========================================