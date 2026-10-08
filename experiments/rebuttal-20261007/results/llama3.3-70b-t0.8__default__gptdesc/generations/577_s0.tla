```
MODULE AlternativeInitialState
EXTENDS BaseSpecification

CONSTANTS NULL

VARIABLES ledger, history, response, committed

Init ==
  /\ ledger = <<>>
  /\ history = <<
    <<NULL, TRUE>>,
    <<NULL, TRUE>>
  >>
  /\ response = [x \in 1..2 |-> NULL]
  /\ committed = [x \in 1..2 |-> TRUE]

Next ==
  MCNextMultiNodeReadsAction

Spec ==
  Init /\ [][Next]_vars
```