---- MODULE MCMultiNodeReadsAlt ----
\* Model-checking wrapper for MCMultiNodeReads with an alternative initial
\* state in which two read-write transactions are already committed.
\*
\* Configuration (MCMultiNodeReadsAlt.cfg):
\*   CONSTANTS HistoryLimit = 11, ViewLimit = 3
\*   SPECIFICATION MCSpecMultiNodeReadsAlt
\*   CHECK_DEADLOCK FALSE
\*   INVARIANTS (inherited from MCMultiNodeReads), e.g.
\*     HistoryTypeOK, LedgerBranchesTypeOK,
\*     AllCommittedObservedInv, OnlyObserveSentRequestsInv,
\*     AllSentRequestsObservedOnceInv, UniqueTxIdsInv, UniqueSeqNumsInv,
\*     CommittedRwSerializableInv, InvalidNotObservedByCommittedInv,
\*     CommittedOrInvalidStrongInv, AtMostOneStatusPerTxInv,
\*     ObservedConsistentWithLedgerInv

EXTENDS MCMultiNodeReads

\* Alternative initial state: two transactions already committed.
\* Ledger branch 1 holds the transaction committed in view 1; ledger branch 2
\* extends it with the transaction committed in view 2.
InitAlt ==
    /\ ledgerBranches =
        << << [view |-> 1, tx |-> 0] >>,
           << [view |-> 1, tx |-> 0], [view |-> 2, tx |-> 1] >> >>
    /\ history =
        << [type |-> RwTxRequest, tx |-> 0],
           [type |-> RwTxRequest, tx |-> 1],
           [type |-> RwTxResponse, tx |-> 0, observed |-> <<>>, tx_id |-> <<1, 1>>],
           [type |-> RwTxResponse, tx |-> 1, observed |-> <<0>>, tx_id |-> <<2, 2>>],
           [type |-> TxStatusReceived, tx_id |-> <<1, 1>>, status |-> CommittedStatus],
           [type |-> TxStatusReceived, tx_id |-> <<2, 2>>, status |-> CommittedStatus] >>

\* Same next-state relation and variables as the parent module,
\* starting from the pre-committed state.
MCSpecMultiNodeReadsAlt ==
    InitAlt /\ [][MCNextMultiNodeReadsAction]_vars

====