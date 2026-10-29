---- MODULE MCMultiNodeReadsAlt ----
\* Alternative initial state for the multi-node reads model.
\* Extends the base model and adds a new initial predicate.

EXTENDS MCMultiNodeReads

\* Initial state with two transactions already committed.
\* The ledger holds both transactions in view 1. The history contains
\* each transaction's request, its response, and a committed-status record.
InitAlt ==
    /\ ledgerBranches = <<
           << [view |-> 1, tx |-> 0],
              [view |-> 1, tx |-> 1] >>
       >>
    /\ history = <<
           [type |-> RwTxRequest, tx |-> 0],
           [type |-> RwTxResponse, tx |-> 0, observed |-> <<0>>, tx_id |-> <<1, 1>>],
           [type |-> RwTxRequest, tx |-> 1],
           [type |-> RwTxResponse, tx |-> 1, observed |-> <<0, 1>>, tx_id |-> <<1, 2>>],
           [type |-> TxStatusReceived, tx_id |-> <<1, 1>>, status |-> CommittedStatus],
           [type |-> TxStatusReceived, tx_id |-> <<1, 2>>, status |-> CommittedStatus]
       >>

\* Temporal specification that starts from the alternative initial state
\* and evolves according to the imported multi-node reads action.
SpecMultiNodeReadsAlt ==
    InitAlt /\ [][MCNextMultiNodeReadsAction]_vars

====