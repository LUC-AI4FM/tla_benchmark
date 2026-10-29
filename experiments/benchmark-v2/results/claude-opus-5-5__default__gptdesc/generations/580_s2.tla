---- MODULE MCSingleNodeReads ----
EXTENDS SingleNodeReads, MCSingleNode

\* Bounded read-only transaction request: only allowed while the
\* history is below the model-checking bound
MCRoTxnRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ RoTxnRequestAction

\* Bounded read-only transaction response: only allowed while the
\* history is below the model-checking bound
MCRoTxnResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ RoTxnResponseAction

\* Combined next-state action: the bounded single-node actions from
\* MCSingleNode together with the bounded read-only transaction actions
MCNextSingleNodeReadsAction ==
    \/ MCNextSingleNodeAction
    \/ MCRoTxnRequestAction
    \/ MCRoTxnResponseAction

\* Safety-style specification
MCSpecSingleNodeReads == Init /\ [][MCNextSingleNodeReadsAction]_vars

====