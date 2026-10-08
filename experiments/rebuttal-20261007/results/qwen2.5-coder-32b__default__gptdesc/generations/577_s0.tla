------------------------------- MODULE AltInitMultiNodeReads -------------------------------
EXTENDS BaseSpec

CONSTANTS Nodes, Transactions

VARIABLES ledgerBranches, history

Init == 
  /\ ledgerBranches = <<>>
  /\ history = <<[transaction |-> Transactions!t1, committed |-> TRUE], [transaction |-> Transactions!t2, committed |-> TRUE]>>

Next == MCNextMultiNodeReadsAction

Spec == Init /\ [][Next]_<<ledgerBranches, history>>

=============================================================================