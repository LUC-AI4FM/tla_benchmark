---- MODULE MCMultiNodeReadsAlt ----
EXTENDS MCMultiNodeReads

\* Alternative initial state in which two transactions are already committed.
\* Ledger branch 1 holds a view-start entry and the two committed transactions.
\* The history holds, for each transaction, its request, its response and a
\* committed-status record.
AltInit ==
    /\ ledgerBranches = <<
            << [view |-> 1],
               [view |-> 1, tx |-> 0],
               [view |-> 1, tx |-> 1] >>
       >>
    /\ history = <<
            [type |-> RwTxRequestType, tx |-> 0],
            [type |-> RwTxResponseType, tx |-> 0, observed |-> <<0>>, tx_id |-> <<1, 2>>],
            [type |-> TxStatusReceivedType, tx_id |-> <<1, 2>>, status |-> CommittedStatus],
            [type |-> RwTxRequestType, tx |-> 1],
            [type |-> RwTxResponseType, tx |-> 1, observed |-> <<0, 1>>, tx_id |-> <<1, 3>>],
            [type |-> TxStatusReceivedType, tx_id |-> <<1, 3>>, status |-> CommittedStatus]
       >>

\* Temporal specification starting from the alternative initial state
AltSpec == AltInit /\ [][MCNextMultiNodeReadsAction]_vars

====