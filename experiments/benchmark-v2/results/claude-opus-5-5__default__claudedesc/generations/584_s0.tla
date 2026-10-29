---------------------------- MODULE SingleNodeReads ----------------------------
\* Extends the SingleNode specification with read-only transactions.
\* Constants, variables (history, ledgerBranches, vars), Init and the
\* read-write transaction actions (NextSingleNodeAction) are inherited.

EXTENDS SingleNode

\* Submit a new read-only transaction.
\* Its identifier is the current length of the history, which is unique.
RoTxRequestAction ==
    /\ history' = Append(
        history,
        [type |-> RoTxRequest,
         tx   |-> Len(history)]
        )
    /\ UNCHANGED ledgerBranches

\* Execute a read-only transaction and respond to it.
\* Unlike read-write transactions, execution and response happen atomically.
RoTxResponseAction ==
    /\ \E i \in DOMAIN history :
        \* Find a read-only request that has not yet been answered
        /\ history[i].type = RoTxRequest
        /\ \A k \in DOMAIN history :
            history[k].type = RoTxResponse => history[k].tx /= history[i].tx
        \* Pick a view (ledger branch) to execute against
        /\ \E view \in DOMAIN ledgerBranches :
            /\ Len(ledgerBranches[view]) > 0
            /\ history' = Append(
                history,
                [type     |-> RoTxResponse,
                 tx       |-> history[i].tx,
                 observed |-> [seqnum \in DOMAIN ledgerBranches[view] |->
                                  ledgerBranches[view][seqnum].tx],
                 tx_id    |-> << ledgerBranches[view][Len(ledgerBranches[view])].view,
                                 Len(ledgerBranches[view]) >>]
                )
    /\ UNCHANGED ledgerBranches

\* Next-state relation: original single-node actions plus read-only actions
NextSingleNodeReadsAction ==
    \/ NextSingleNodeAction
    \/ RoTxRequestAction
    \/ RoTxResponseAction

\* Temporal specification (no fairness conditions)
SpecSingleNodeReads == Init /\ [][NextSingleNodeReadsAction]_vars

=============================================================================