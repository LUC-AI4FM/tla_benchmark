---------------------------- MODULE MCSingleNode ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    FirstBranch,
    HistoryLimit,
    RwTxRequest,
    RwTxResponse,
    RoTxRequest,
    RoTxResponse,
    TxStatusReceived,
    CommittedStatus,
    InvalidStatus

VARIABLES history, ledger, commitIndex

vars == <<history, ledger, commitIndex>>

-----------------------------------------------------------------------------
\* Helpers

Range(s) == {s[i] : i \in DOMAIN s}

IsPrefix(a, b) == Len(a) <= Len(b) /\ SubSeq(b, 1, Len(a)) = a

ResponseIdxs ==
    {i \in DOMAIN history : history[i].type \in {RwTxResponse, RoTxResponse}}

RwResponseIdxs ==
    {i \in DOMAIN history : history[i].type = RwTxResponse}

RespondedTxs == {history[i].tx : i \in ResponseIdxs}

StatusIdxs(s) ==
    {i \in DOMAIN history : history[i].type = TxStatusReceived /\ history[i].status = s}

CommittedTxIds == {history[i].tx_id : i \in StatusIdxs(CommittedStatus)}

InvalidTxIds == {history[i].tx_id : i \in StatusIdxs(InvalidStatus)}

CommittedRwResponseIdxs ==
    {i \in RwResponseIdxs : history[i].tx_id \in CommittedTxIds}

ReqType(t) == IF t = RwTxResponse THEN RwTxRequest ELSE RoTxRequest

-----------------------------------------------------------------------------
\* Specification

Init ==
    /\ history = <<>>
    /\ ledger = <<>>
    /\ commitIndex = 0

\* Client submits a read-write transaction request
RwTxRequestAction ==
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> Len(history) + 1])
    /\ UNCHANGED <<ledger, commitIndex>>

\* Node executes a pending read-write transaction (internal step)
RwTxExecuteAction ==
    \E i \in DOMAIN history:
        /\ history[i].type = RwTxRequest
        /\ history[i].tx \notin Range(ledger)
        /\ ledger' = Append(ledger, history[i].tx)
        /\ UNCHANGED <<history, commitIndex>>

\* Node responds to an executed read-write transaction
RwTxResponseAction ==
    \E i \in DOMAIN ledger:
        /\ ledger[i] \notin RespondedTxs
        /\ history' = Append(history,
                [type |-> RwTxResponse,
                 tx |-> ledger[i],
                 observed |-> SubSeq(ledger, 1, i),
                 tx_id |-> <<FirstBranch, i>>])
        /\ UNCHANGED <<ledger, commitIndex>>

\* Client submits a read-only transaction request
RoTxRequestAction ==
    /\ history' = Append(history, [type |-> RoTxRequest, tx |-> Len(history) + 1])
    /\ UNCHANGED <<ledger, commitIndex>>

\* Node executes and responds to a read-only transaction
RoTxResponseAction ==
    \E i \in DOMAIN history:
        /\ history[i].type = RoTxRequest
        /\ history[i].tx \notin RespondedTxs
        /\ Len(ledger) > 0
        /\ history' = Append(history,
                [type |-> RoTxResponse,
                 tx |-> history[i].tx,
                 observed |-> ledger,
                 tx_id |-> <<FirstBranch, Len(ledger)>>])
        /\ UNCHANGED <<ledger, commitIndex>>

\* Node commits the next ledger entry (internal step)
CommitAction ==
    /\ commitIndex < Len(ledger)
    /\ commitIndex' = commitIndex + 1
    /\ UNCHANGED <<history, ledger>>

\* Client queries status of a transaction and receives committed status
StatusCommittedResponseAction ==
    \E i \in 1..commitIndex:
        /\ \E j \in RwResponseIdxs : history[j].tx_id = <<FirstBranch, i>>
        /\ history' = Append(history,
                [type |-> TxStatusReceived,
                 tx_id |-> <<FirstBranch, i>>,
                 status |-> CommittedStatus])
        /\ UNCHANGED <<ledger, commitIndex>>

HistoryActions ==
    \/ RwTxRequestAction
    \/ RwTxResponseAction
    \/ RoTxRequestAction
    \/ RoTxResponseAction
    \/ StatusCommittedResponseAction

InternalActions ==
    \/ RwTxExecuteAction
    \/ CommitAction

Next == HistoryActions \/ InternalActions

SpecSingleNode == Init /\ [][Next]_vars

\* Bounded next: only history-extending actions are restricted
MCNext ==
    \/ /\ Len(history) < HistoryLimit
       /\ HistoryActions
    \/ InternalActions

MCSpecSingleNode == Init /\ [][MCNext]_vars

-----------------------------------------------------------------------------
\* Invariants

AllReceivedIsFirstSentInv ==
    \A i \in ResponseIdxs:
        \E j \in 1..(i - 1):
            /\ history[j].type = ReqType(history[i].type)
            /\ history[j].tx = history[i].tx

AllCommittedObservedInv ==
    \A i, j \in CommittedRwResponseIdxs:
        history[i].tx_id[2] < history[j].tx_id[2]
            => history[i].tx \in Range(history[j].observed)

OnlyObserveSentRequestsInv ==
    \A i \in ResponseIdxs:
        \A t \in Range(history[i].observed):
            \E j \in 1..(i - 1):
                /\ history[j].type = RwTxRequest
                /\ history[j].tx = t

UniqueTxsInv ==
    \A i, j \in ResponseIdxs:
        history[i].tx = history[j].tx => i = j

UniqueTxIdsInv ==
    \A i, j \in RwResponseIdxs:
        history[i].tx_id = history[j].tx_id => i = j

UniqueSeqNumsInv ==
    \A i, j \in RwResponseIdxs:
        history[i].tx_id[2] = history[j].tx_id[2] => i = j

CommittedOrInvalidStrongInv ==
    CommittedTxIds \cap InvalidTxIds = {}

RwSerializableInv ==
    \A i, j \in RwResponseIdxs:
        \/ IsPrefix(history[i].observed, history[j].observed)
        \/ IsPrefix(history[j].observed, history[i].observed)

CommittedRwSerializableInv ==
    \A i, j \in CommittedRwResponseIdxs:
        \/ IsPrefix(history[i].observed, history[j].observed)
        \/ IsPrefix(history[j].observed, history[i].observed)

InvalidNotObservedInv ==
    \A i \in RwResponseIdxs:
        history[i].tx_id \in InvalidTxIds =>
            \A j \in ResponseIdxs:
                history[j].tx /= history[i].tx =>
                    history[i].tx \notin Range(history[j].observed)

InvalidNotObservedByCommittedInv ==
    \A i \in RwResponseIdxs:
        history[i].tx_id \in InvalidTxIds =>
            \A j \in CommittedRwResponseIdxs:
                history[j].tx /= history[i].tx =>
                    history[i].tx \notin Range(history[j].observed)

AtMostOnceObservedInv ==
    \A i \in ResponseIdxs:
        Len(history[i].observed) = Cardinality(Range(history[i].observed))

=============================================================================