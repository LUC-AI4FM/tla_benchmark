---- MODULE MCMultiNode ----
EXTENDS MultiNode, TLC, Sequences, Naturals

CONSTANT ViewLimit

ASSUME ViewLimit \in Nat

\* Bound on the number of view changes (ledger branches)
MCTruncateLedgerAction ==
    /\ Len(ledgerBranches) < ViewLimit
    /\ TruncateLedgerAction

\* Bound on the number of client requests recorded in the history
MCRwTxRequestAction ==
    /\ Len(history) < 8
    /\ RwTxRequestAction

\* Bound on transactions appended by other nodes, also limited by views
MCAppendOtherTxnAction ==
    /\ Len(ledgerBranches) <= ViewLimit
    /\ Len(history) < 8
    /\ AppendOtherTxnAction

MCNextMultiNodeAction ==
    \/ MCRwTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ StatusCommittedResponseAction
    \/ StatusInvalidResponseAction
    \/ MCAppendOtherTxnAction
    \/ MCTruncateLedgerAction

MCSpecMultiNode == Init /\ [][MCNextMultiNodeAction]_vars

====