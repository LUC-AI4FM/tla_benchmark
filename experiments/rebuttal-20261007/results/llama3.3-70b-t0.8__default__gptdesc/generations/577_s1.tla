```
MODULE AlternativeInitialState
EXTENDS BaseSpecification

CONSTANTS null

VARIABLES ledgerBranches, history, response, committedStatus

Init == 
  /\ ledgerBranches = <<1, 2>>
  /\ history = <<[response |-> <<1, 2>>, committedStatus |-> <<TRUE, TRUE>>]>>
  /\ response = <<1, 2>>
  /\ committedStatus = <<TRUE, TRUE>>

Next == 
  <>[MCNextMultiNodeReadsAction]_vars

Spec == 
  Init /\ [][Next]_vars
```