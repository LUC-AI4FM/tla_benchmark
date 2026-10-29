------------------------------- MODULE MCPaxos -------------------------------
EXTENDS Integers, FiniteSets

-----------------------------------------------------------------------------
(* Single-value consensus abstraction.                                     *)
-----------------------------------------------------------------------------
---------------------------- MODULE Consensus -------------------------------
CONSTANT Value
VARIABLE chosen

CTypeOK == chosen \subseteq Value

CInit == chosen = {}

CNext == /\ chosen = {}
         /\ \E v \in Value : chosen' = {v}

CSpec == CInit /\ [][CNext]_chosen

CInv == /\ CTypeOK
        /\ Cardinality(chosen) \leq 1
=============================================================================