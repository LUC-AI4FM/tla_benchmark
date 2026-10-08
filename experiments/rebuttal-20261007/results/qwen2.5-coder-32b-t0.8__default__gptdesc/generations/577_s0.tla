------------------------------- MODULE AlternativeInitialState -------------------------------

EXTENDS MultiNodeReadsBase

CONSTANTS Nodes, Transactions

VARIABLES ledger, history

Init == 
    /\ ledger = [n \in Nodes |-> {}]
    /\ history = <<{tid: 1; response: "success"; committed: TRUE}, {tid: 2; response: "success"; committed: TRUE}>>
    
Next == MCNextMultiNodeReadsAction

Spec == 
    /\ Init
    /\ [][Next]_<<ledger, history>>

=============================================================================