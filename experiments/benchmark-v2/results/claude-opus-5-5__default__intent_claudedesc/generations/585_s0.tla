---------------------------- MODULE SingleNodeCCF ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    RequestLimit,   \* maximum number of client read-write requests (bounds the model)
    LedgerLimit     \* maximum ledger length for background appends (bounds the model)

ASSUME RequestLimit \in Nat /\ LedgerLimit \in Nat

\* Single node: there is exactly one view, so no elections or view changes occur
FirstView == 1
ViewLimit == 1
Views == FirstView..ViewLimit
CurrentView == ViewLimit

\* Transaction identifiers for client requests
Txs == 0..RequestLimit

\* Sequence numbers
SeqNums == Nat \ {0}

\* Transaction IDs: <<view, seqnum>>
TxIDs == Views \X SeqNums

\* Event types in the external history
RwTxRequest == "RwTxRequest"
RwTxResponse == "RwTxResponse"
TxStatusReceived == "TxStatusReceived"

\* Transaction statuses
CommittedStatus == "CommittedStatus"
InvalidStatus == "InvalidStatus"
TxStatuses == {CommittedStatus, InvalidStatus}

VARIABLES
    history,         \* sequence of externally observable events
    ledgerBranches   \* function from view to the ledger branch for that view

vars == <<history, ledgerBranches>>

-----------------------------------------------------------------------------
\* Helpers

IsPrefix(s, t) == Len(s) <= Len(t) /\ SubSeq(t, 1, Len(s)) = s

HasTx(entry) == "tx" \in DOMAIN entry

\* The sequence of client transactions recorded in positions 1..n of a ledger
TxsInPrefix(ledger, n) ==
    LET prefix == SubSeq(ledger, 1, n)
        withTx == SelectSeq(prefix, HasTx)
    IN [k \in 1..Len(withTx) |-> withTx[k].tx]

Range(s) == {s[k] : k \in DOMAIN s}

RequestIndices == {i \in DOMAIN history : history[i].type = RwTxRequest}
ResponseIndices == {i \in DOMAIN history : history[i].type = RwTxResponse}
StatusIndices == {i \in DOMAIN history : history[i].type = TxStatusReceived}

NextRequestId == Cardinality(RequestIndices)

LedgerEntries == [view : Views] \cup [view : Views, tx : Txs]

\* Is the transaction already in some ledger branch?
TxInLedger(tx) ==
    \E v \in Views : \E s \in DOMAIN ledgerBranches[v] :
        HasTx(ledgerBranches[v][s]) /\ ledgerBranches[v][s].tx = tx

-----------------------------------------------------------------------------
\* Initial state

Init ==
    /\ history = <<>>
    /\ ledgerBranches = [v \in Views |-> <<>>]

-----------------------------------------------------------------------------
\* Actions

\* A client submits a new read-write transaction with a unique identifier
RwTxRequestAction ==
    /\ NextRequestId < RequestLimit
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> NextRequestId])
    /\ UNCHANGED ledgerBranches

\* A requested transaction is executed by appending it to a ledger branch
RwTxExecuteAction ==
    \E i \in RequestIndices :
        /\ ~TxInLedger(history[i].tx)
        /\ \E v \in Views :
            ledgerBranches' = [ledgerBranches EXCEPT ![v] =
                                  Append(@, [view |-> v, tx |-> history[i].tx])]
        /\ UNCHANGED history

\* The service responds with the transaction ID and observed preceding txs
RwTxResponseAction ==
    \E i \in RequestIndices :
        /\ ~\E j \in ResponseIndices : history[j].tx = history[i].tx
        /\ \E v \in Views : \E s \in DOMAIN ledgerBranches[v] :
            /\ HasTx(ledgerBranches[v][s])
            /\ ledgerBranches[v][s].tx = history[i].tx
            /\ history' = Append(history,
                  [type     |-> RwTxResponse,
                   tx       |-> history[i].tx,
                   observed |-> TxsInPrefix(ledgerBranches[v], s - 1),
                   tx_id    |-> <<ledgerBranches[v][s].view, s>>])
        /\ UNCHANGED ledgerBranches

\* The service reports that a transaction is committed
StatusCommittedResponseAction ==
    \E i \in ResponseIndices :
        LET view == history[i].tx_id[1]
            seqnum == history[i].tx_id[2]
        IN
        /\ ~\E j \in StatusIndices : history[j].tx_id = history[i].tx_id
        /\ seqnum \in DOMAIN ledgerBranches[CurrentView]
        /\ ledgerBranches[CurrentView][seqnum].view = view
        /\ history' = Append(history,
              [type   |-> TxStatusReceived,
               tx_id  |-> history[i].tx_id,
               status |-> CommittedStatus])
        /\ UNCHANGED ledgerBranches

\* Other (untracked) transactions appended to the ledger
AppendOtherTxnAction ==
    \E v \in Views :
        /\ Len(ledgerBranches[v]) < LedgerLimit
        /\ ledgerBranches' = [ledgerBranches EXCEPT ![v] = Append(@, [view |-> v])]
        /\ UNCHANGED history

Next ==
    \/ RwTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ StatusCommittedResponseAction
    \/ AppendOtherTxnAction

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Safety invariants

LedgerTypeOK ==
    /\ DOMAIN ledgerBranches = Views
    /\ \A v \in Views :
        /\ ledgerBranches[v] \in Seq(LedgerEntries)
        /\ \A s \in DOMAIN ledgerBranches[v] :
            /\ ledgerBranches[v][s].view \in Views
            /\ HasTx(ledgerBranches[v][s]) => ledgerBranches[v][s].tx \in Txs

HistoryTypeOK ==
    \A i \in DOMAIN history :
        \/ /\ history[i].type = RwTxRequest
           /\ history[i].tx \in Txs
        \/ /\ history[i].type = RwTxResponse
           /\ history[i].tx \in Txs
           /\ history[i].tx_id \in TxIDs
           /\ Range(history[i].observed) \subseteq Txs
        \/ /\ history[i].type = TxStatusReceived
           /\ history[i].tx_id \in TxIDs
           /\ history[i].status \in TxStatuses

TypeOK == LedgerTypeOK /\ HistoryTypeOK

\* Each transaction appears at most once across all ledgers
UniqueTxsInLedgerInv ==
    \A v1, v2 \in Views :
        \A s1 \in DOMAIN ledgerBranches[v1], s2 \in DOMAIN ledgerBranches[v2] :
            (/\ HasTx(ledgerBranches[v1][s1])
             /\ HasTx(ledgerBranches[v2][s2])
             /\ ledgerBranches[v1][s1].tx = ledgerBranches[v2][s2].tx)
            => (v1 = v2 /\ s1 = s2)

\* Request identifiers are unique
UniqueRequestsInv ==
    \A i, j \in RequestIndices : history[i].tx = history[j].tx => i = j

\* Every response is preceded by its request; at most one response per tx
ResponseAfterRequestInv ==
    \A i \in ResponseIndices :
        /\ \E j \in RequestIndices : j < i /\ history[j].tx = history[i].tx
        /\ \A k \in ResponseIndices : history[k].tx = history[i].tx => k = i

\* Every status notification follows a response with that tx ID
StatusAfterResponseInv ==
    \A i \in StatusIndices :
        \E j \in ResponseIndices : j < i /\ history[j].tx_id = history[i].tx_id

\* No transaction is ever reported invalid (no rollbacks in single node)
InvalidNotObservedInv ==
    \A i \in StatusIndices : history[i].status /= InvalidStatus

\* Once a tx ID is returned, it remains valid permanently in the current ledger
AllTxIdsRemainValidInv ==
    \A i \in ResponseIndices :
        LET s == history[i].tx_id[2]
        IN /\ s \in DOMAIN ledgerBranches[CurrentView]
           /\ ledgerBranches[CurrentView][s].view = history[i].tx_id[1]
           /\ HasTx(ledgerBranches[CurrentView][s])
           /\ ledgerBranches[CurrentView][s].tx = history[i].tx

CommittedResponses ==
    {i \in ResponseIndices :
        \E j \in StatusIndices :
            /\ history[j].tx_id = history[i].tx_id
            /\ history[j].status = CommittedStatus}

\* Distinct committed transactions have distinct tx IDs
UniqueCommittedTxIdsInv ==
    \A i, j \in CommittedResponses :
        history[i].tx_id = history[j].tx_id => history[i].tx = history[j].tx

\* Committed transactions form a linear order consistent with observations
CommittedLinearizableInv ==
    \A i, j \in CommittedResponses :
        history[i].tx_id[2] < history[j].tx_id[2]
        => history[i].tx \in Range(history[j].observed)

\* Every observed tx was requested and not observed after itself
ObservedConsistencyInv ==
    \A i \in ResponseIndices :
        /\ history[i].tx \notin Range(history[i].observed)
        /\ \A t \in Range(history[i].observed) :
              \E j \in RequestIndices : history[j].tx = t

ExternalHistoryInv ==
    /\ UniqueRequestsInv
    /\ ResponseAfterRequestInv
    /\ StatusAfterResponseInv
    /\ InvalidNotObservedInv
    /\ UniqueCommittedTxIdsInv
    /\ CommittedLinearizableInv
    /\ ObservedConsistencyInv

Inv ==
    /\ TypeOK
    /\ UniqueTxsInLedgerInv
    /\ AllTxIdsRemainValidInv
    /\ ExternalHistoryInv

-----------------------------------------------------------------------------
\* Action (temporal) properties

\* Each ledger branch is append-only
MonotonicLedgerProp ==
    [][\A v \in Views : IsPrefix(ledgerBranches[v], ledgerBranches'[v])]_vars

\* The history is append-only
MonotonicHistoryProp ==
    [][IsPrefix(history, history')]_vars

THEOREM Spec => []Inv
THEOREM Spec => MonotonicLedgerProp /\ MonotonicHistoryProp

=============================================================================