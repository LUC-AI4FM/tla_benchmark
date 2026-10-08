```tla
MODULE AltInitMultiNodeReads

EXTENDS BaseModule

CONSTANTS 
    Nodes, Transactions, LedgerBranches, History

VARIABLES 
    branches, history

Init == 
    /\ branches = [n \in Nodes |-> [b \in LedgerBranches |-> {}]]
    /\ history = <<[t \in Transactions |-> IF t \in {T1, T2} THEN TRUE ELSE FALSE]>>
    
Next ==
    MCNextMultiNodeReadsAction

Spec == 
    /\ Init
    /\ [][Next]_<<branches, history>>
```