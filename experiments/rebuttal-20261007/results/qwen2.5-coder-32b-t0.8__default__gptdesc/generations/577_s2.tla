------------------------------- MODULE AlternativeInitState -------------------------------
EXTENDS BaseModule

CONSTANTS Nodes, Transactions

VARIABLES ledgerBranches, history

Init == 
  /\ ledgerBranches = << >> 
  /\ history = << [transaction |-> Transactions[1], committed |-> TRUE], 
                  [transaction |-> Transactions[2], committed |-> TRUE] >>

Next == MCNextMultiNodeReadsAction

Spec == Init /\ [][Next]_<<ledgerBranches, history>>

=======================================================================================