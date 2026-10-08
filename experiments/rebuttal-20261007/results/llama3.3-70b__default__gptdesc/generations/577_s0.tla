```
MODULE AlternativeInitialState
EXTENDS BaseSpecification

CONSTANTS CommittedTransactions, HistorySequence

VARIABLES ledgerBranches, history, responseRecords, committedStatusRecords

Init == (* Initial predicate for alternative initial state *)
        /\ ledgerBranches = << "branch1", "branch2" >>
        /\ history = << [ transaction1 |-> "committed", transaction2 |-> "committed" ] >>
        /\ responseRecords = << [ transaction1 |-> "response1", transaction2 |-> "response2" ] >>
        /\ committedStatusRecords = << [ transaction1 |-> TRUE, transaction2 |-> TRUE ] >>

Next == (* Stuttering form of MCNextMultiNodeReadsAction *)
        [](MCNextMultiNodeReadsAction)_vars

Spec == Init /\ [][Next]_vars

THEOREM Spec => []Init
```