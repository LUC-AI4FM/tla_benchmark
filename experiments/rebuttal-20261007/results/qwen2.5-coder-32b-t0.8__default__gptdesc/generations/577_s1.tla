------------------------------- MODULE AlternativeInit -------------------------------

EXTENDS MCBaseModule

CONSTANTS 
    \* Constants as defined in MCBaseModule

VARIABLES 
    ledgerBranches, history, vars

Init == /\ ledgerBranches = [branch \in BRANCHES |-> [node \in NODES |-> <<>>]]
        /\ history = <<[transaction |-> trans1, committed |-> TRUE], 
                        [transaction |-> trans2, committed |-> TRUE]>>
        /\ vars = initialVars

Next == MCNextMultiNodeReadsAction

Spec == Init /\ [][Next]_<<ledgerBranches, history, vars>>

=============================================================================