```
MODULE AlternativeInitialState
EXTENDS BaseSpecification

CONSTANTS Null

VARIABLES ledger, history, response, committed

Init == 
  (/* Initial two transactions are already committed */ 
   /\ ledger = <<>>
   /\ history = <<["tx1", "committed"], ["tx2", "committed"]>>
   /\ response = <<>>
   /\ committed = <<True, True>>)

Next == MCNextMultiNodeReadsAction

Spec == Init /\ [][Next]_vars

THEOREM Spec => []Init
```