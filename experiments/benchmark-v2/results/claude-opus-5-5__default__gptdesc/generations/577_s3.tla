---- MODULE MCMultiNodeReadsAlt ----
EXTENDS MCMultiNodeReads

\* Alternative initial state where two transactions have already been committed
AltInit ==
    /\ ledgerBranches = <<
        << [view |-> 1, tx |-> 0], [view |-> 1, tx |-> 1] >>
        >>
    /\ history = <<
        [type |-> RwTxRequest, tx |-> 0],
        [type |-> RwTxRequest, tx |-> 1],
        [type |-> RwTxResponse, tx |-> 0, tx_id |-> <<1, 1>>, observed |-> <<0>>],
        [type |-> RwTxResponse, tx |-> 1, tx_id |-> <<1, 2>>, observed |-> <<0, 1>>],
        [type |-> TxStatusReceived, tx_id |-> <<1, 1>>, status |-> CommittedStatus],
        [type |-> TxStatusReceived, tx_id |-> <<1, 2>>, status |-> CommittedStatus]
        >>

AltSpec == AltInit /\ [][MCNextMultiNodeReadsAction]_vars

====