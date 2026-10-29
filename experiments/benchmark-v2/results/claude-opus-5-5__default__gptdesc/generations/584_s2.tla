---- MODULE SingleNodeReads ----
\* Expanding SingleNode to add read-only transactions

EXTENDS SingleNode

\* Submit new read-only transaction
RoTxRequestAction ==
    /\ history' = Append(
        history,
        [type |-> RoTxRequest, tx |-> NextRequestId]
        )
    /\ UNCHANGED ledgerBranches

\* Execute a read-only transaction
\* Note that:
\* - read-only transactions are assumed to always be forwarded
\* - the read and the response happen in one atomic step
\* - the response observes the contents of some ledger branch
RoTxResponseAction ==
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RoTxRequest
        /\ \A j \in DOMAIN history :
            history[j].type = RoTxResponse => history[j].tx # history[i].tx
        /\ \E view \in DOMAIN ledgerBranches :
            /\ Len(ledgerBranches[view]) > 0
            /\ history' = Append(
                history,
                [type |-> RoTxResponse,
                 tx |-> history[i].tx,
                 observed |-> [seqnum \in DOMAIN ledgerBranches[view] |->
                                  ledgerBranches[view][seqnum].tx],
                 tx_id |-> <<ledgerBranches[view][Len(ledgerBranches[view])].view,
                             Len(ledgerBranches[view])>>]
                )
    /\ UNCHANGED ledgerBranches

NextSingleNodeReadsAction ==
    \/ NextSingleNodeAction
    \/ RoTxRequestAction
    \/ RoTxResponseAction

SpecSingleNodeReads == Init /\ [][NextSingleNodeReadsAction]_vars

====