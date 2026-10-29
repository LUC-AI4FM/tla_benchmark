------------------------------- MODULE MCPaxos -------------------------------
EXTENDS Integers, FiniteSets

-----------------------------------------------------------------------------
(* Single-value consensus abstraction, refined by Paxos below.              *)
-----------------------------------------------------------------------------
---------------------------- MODULE Consensus -------------------------------
CONSTANT Value
VARIABLE chosen

TypeOK == chosen \subseteq Value

Init == chosen = {}

Next == /\ chosen = {}
        /\ \E v \in Value : chosen' = {v}

Spec == Init /\ [][Next]_chosen

Inv == /\ TypeOK
       /\ \A v1, v2 \in chosen : v1 = v2
=============================================================================