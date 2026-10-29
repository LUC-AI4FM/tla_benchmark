---- MODULE MCMultiNodeReadsAlt ----
EXTENDS MCMultiNodeReads

\* Alternative initial state where two transactions are already committed
InitAlt ==
    /\ ledgerBranches = [ x \in Views |->
            IF x = 1
            THEN << [view |-> 1, tx |-> 0],
                    [view |-> 1, tx |-> 1] >>
            ELSE << >> ]
    /\ history = <<
        [type |-> RwTxRequest, tx |-> 0],
        [type |-> RwTxResponse, tx |-> 0, observed |-> <<0>>, tx_id |-> <<1, 1>>],
        [type |-> TxStatusReceived, tx_id |-> <<1, 1>>, status |-> CommittedStatus],
        [type |-> RwTxRequest, tx |-> 1],
        [type |-> RwTxResponse, tx |-> 1, observed |-> <<0, 1>>, tx_id |-> <<1, 2>>],
        [type |-> TxStatusReceived, tx_id |-> <<1, 2>>, status |-> CommittedStatus]
        >>

SpecMultiNodeReadsAlt ==
    InitAlt /\ [][MCNextMultiNodeReadsAction]_vars

====