```
MODULE AltInitialState
EXTENDS MultiNodeReadsBase, Sequences, TLC

CONSTANTS BRANCHES

VARIABLES history, ledgerBranches

vars == <<history, ledgerBranches>>

AlternativeInit ==
  /\ history = << [txnId |-> 1, status |-> "committed", response |-> [ok |-> TRUE] ],
                 [txnId |-> 2, status |-> "committed", response |-> [ok |-> TRUE]] >>
  /\ ledgerBranches = [b \in BRANCHES -> []]

Init == AlternativeInit

Next == MCNextMultiNodeReadsAction

Spec == Init /\ [][Next]_vars
```