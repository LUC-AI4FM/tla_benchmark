```tla
MODULE AlternativeInitialState

EXTENDS BaseModule

CONSTANTS Nodes, Transactions, LedgerBranches, HistorySeq

VARIABLES ledger, history

Init == 
  /\ ledger = <<[branch \in LedgerBranches |-> []], [branch \in LedgerBranches |-> []]>>
  /\ history = <<<<[transaction \in Transactions |-> FALSE]>>, <<[transaction \in Transactions |-> TRUE]>>>> 

Next == MCNextMultiNodeReadsAction

Spec ==
  /\ Init
  /\ [][Next]_<<ledger, history>>

INVARIANT_STUB ==
  /\ TRUE  (* Add any specific invariants here *)

LIVENESS_STUB ==
  \/ <<>>  (* Add any specific liveness properties here *)

WF_vars == 
  WF_[MCNextMultiNodeReadsAction]_vars

SpecWithFairness ==
  /\ Spec
  /\ SF_vars
```