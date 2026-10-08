```
MODULE AlternativeInitialState
EXTENDS BaseSpecification

CONSTANTS CommittedTransactions, Transactions
VARIABLES ledgerBranches, history, responseRecords, committedStatusRecords

Init == (* Initialize ledger branches and history with two transactions already committed *)
        /\ ledgerBranches = <<1, 2>>
        /\ history = << [tx1 |-> "committed", tx2 |-> "committed" ] >>
        /\ responseRecords = <<[tx1 |-> "success"], [tx2 |-> "success"]>>
        /\ committedStatusRecords = <<[tx1 |-> TRUE], [tx2 |-> TRUE]>>

Next == (* Apply the MCNextMultiNodeReadsAction to evolve the state *)
        [][MCNextMultiNodeReadsAction]_vars

Spec == Init /\ [][Next]_vars

THEOREM Spec => []Init
```