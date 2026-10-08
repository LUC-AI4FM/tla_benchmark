```
MODULE AltInitialMultiNodeReads
EXTENDS BaseSpec

CONSTANTS Tx1, Tx2

VARIABLES ledgerBranches, history

(* Alternative initial state *)
AltInitial ==
    /\ ledgerBranches = [node \in 1..2 |-> []]
    /\ history =
          <<[tx |-> Tx1, status |-> "committed"],
            [tx |-> Tx2, status |-> "committed"]>>

Init == BaseSpec.Init /\ AltInitial

Next == MCNextMultiNodeReadsAction

vars == {ledgerBranches, history}

Spec == Init /\ [][Next]_vars
```