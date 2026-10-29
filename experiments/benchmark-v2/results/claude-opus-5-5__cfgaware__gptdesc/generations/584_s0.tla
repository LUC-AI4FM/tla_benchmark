---- MODULE SingleNodeReads ----
\* Abstract specification of a single node system, extended with read-only transactions
EXTENDS SingleNode

\* Submit a new read-only transaction request
RoTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ history' = Append(
        history,
        [type |-> RoTxRequest, tx |-> NextRequestId]
        )
    /\ UNCHANGED ledgerBranches

\* Response to a read-only transaction request.
\* Assumes read-only transactions are always forwarded.
\* The read and the response happen in one atomic step.
RoTxResponseAction ==
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RoTxRequest
        /\ \A j \in DOMAIN history :
            history[j].type = RoTxResponse => history[j].tx /= history[i].tx
        /\ \E view \in DOMAIN ledgerBranches :
            /\ Len(ledgerBranches[view]) > 0
            /\ history' = Append(
                history,
                [type |-> RoTxResponse,
                 tx |-> history[i].tx,
                 observed |-> [seqnum \in DOMAIN ledgerBranches[view] |->
                                 ledgerBranches[view][seqnum].tx],
                 tx_id |-> << ledgerBranches[view][Len(ledgerBranches[view])].view,
                              Len(ledgerBranches[view]) >>]
                )
    /\ UNCHANGED ledgerBranches

NextSingleNodeReadsAction ==
    \/ NextSingleNodeAction
    \/ RoTxRequestAction
    \/ RoTxResponseAction

SpecSingleNodeReads == Init /\ [][NextSingleNodeReadsAction]_vars

====