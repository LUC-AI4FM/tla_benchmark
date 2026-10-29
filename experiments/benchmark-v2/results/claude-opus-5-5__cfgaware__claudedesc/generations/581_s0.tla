---------------------------- MODULE MCSingleNode ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    HistoryLimit,
    FirstBranch,
    RwTxRequest,
    RwTxResponse,
    RoTxRequest,
    RoTxResponse,
    TxStatusReceived,
    CommittedStatus,
    InvalidStatus

VARIABLES history, ledgerBranches

vars == <<history, ledgerBranches>>

\* ---------------------------------------------------------------------------
\* Helpers
\* ---------------------------------------------------------------------------

ledger == ledgerBranches[FirstBranch]

LedgerTxs(k) == [j \in 1..k |-> ledger[j].tx]

IsPrefix(s, t) == Len(s) <= Len(t) /\ SubSeq(t, 1, Len(s)) = s

Range(s) == {s[i] : i \in DOMAIN s}

RequestTypes == {RwTxRequest, RoTxRequest}
ResponseTypes == {RwTxResponse, RoTxResponse}

RequestedTxs == {history[i].tx : i \in {k \in DOMAIN history : history[k].type \in RequestTypes}}

RwResponseIdx == {i \in DOMAIN history : history[i].type = RwTxResponse}
ResponseIdx == {i \in DOMAIN history : history[i].type \in ResponseTypes}
StatusIdx == {i \in DOMAIN history : history[i].type = TxStatusReceived}

HasStatus(tid, st) ==
    \E k \in StatusIdx : history[k].tx_id = tid /\ history[k].status = st

Committed(tid) == HasStatus(tid, CommittedStatus)
Invalid(tid) == HasStatus(tid, InvalidStatus)

CommittedRwIdx == {i \in RwResponseIdx : Committed(history[i].tx_id)}
InvalidRwIdx == {i \in RwResponseIdx : Invalid(history[i].tx_id)}

\* ---------------------------------------------------------------------------
\* Base SingleNode behaviour
\* ---------------------------------------------------------------------------

Init ==
    /\ history = <<>>
    /\ ledgerBranches = [b \in {FirstBranch} |-> <<>>]

RwTxRequestAction ==
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> Len(history) + 1])
    /\ UNCHANGED ledgerBranches

RwTxExecuteAction ==
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxRequest
        /\ history[i].tx \notin {ledger[k].tx : k \in DOMAIN ledger}
        /\ ledgerBranches' = [ledgerBranches EXCEPT ![FirstBranch] =
                Append(@, [view |-> FirstBranch, tx |-> history[i].tx])]
    /\ UNCHANGED history

RwTxResponseAction ==
    /\ \E i \in DOMAIN ledger :
        /\ ~ \E k \in DOMAIN history :
                /\ history[k].type = RwTxResponse
                /\ history[k].tx = ledger[i].tx
        /\ history' = Append(history,
                [type |-> RwTxResponse,
                 tx |-> ledger[i].tx,
                 observed |-> LedgerTxs(i),
                 tx_id |-> <<FirstBranch, i>>])
    /\ UNCHANGED ledgerBranches

StatusCommittedResponseAction ==
    /\ \E i \in RwResponseIdx :
        /\ ~ \E k \in StatusIdx : history[k].tx_id = history[i].tx_id
        /\ history[i].tx_id[2] \in DOMAIN ledger
        /\ history' = Append(history,
                [type |-> TxStatusReceived,
                 tx_id |-> history[i].tx_id,
                 status |-> CommittedStatus])
    /\ UNCHANGED ledgerBranches

\* ---------------------------------------------------------------------------
\* Bounded versions for model checking
\* ---------------------------------------------------------------------------

MCRwTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ RwTxRequestAction

MCRwTxResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ RwTxResponseAction

MCStatusCommittedResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ StatusCommittedResponseAction

MCNextSingleNode ==
    \/ MCRwTxRequestAction
    \/ RwTxExecuteAction
    \/ MCRwTxResponseAction
    \/ MCStatusCommittedResponseAction

MCSpecSingleNode == Init /\ [][MCNextSingleNode]_vars

\* ---------------------------------------------------------------------------
\* Invariants
\* ---------------------------------------------------------------------------

AllReceivedIsFirstSentInv ==
    \A i \in ResponseIdx :
        \E j \in DOMAIN history :
            /\ j < i
            /\ history[j].type \in RequestTypes
            /\ history[j].tx = history[i].tx

AllCommittedObservedInv ==
    \A i, j \in CommittedRwIdx :
        history[i].tx_id[2] < history[j].tx_id[2]
            => history[i].tx \in Range(history[j].observed)

OnlyObserveSentRequestsInv ==
    \A i \in ResponseIdx :
        Range(history[i].observed) \subseteq RequestedTxs

UniqueTxsInv ==
    \A i, j \in ResponseIdx :
        (i # j) => history[i].tx # history[j].tx

UniqueTxIdsInv ==
    \A i, j \in RwResponseIdx :
        (i # j) => history[i].tx_id # history[j].tx_id

UniqueSeqNumsInv ==
    \A i, j \in CommittedRwIdx :
        (i # j) => history[i].tx_id[2] # history[j].tx_id[2]

CommittedOrInvalidStrongInv ==
    \A i, j \in StatusIdx :
        history[i].tx_id = history[j].tx_id
            => history[i].status = history[j].status

RwSerializableInv ==
    \A i, j \in RwResponseIdx :
        \/ IsPrefix(history[i].observed, history[j].observed)
        \/ IsPrefix(history[j].observed, history[i].observed)

CommittedRwSerializableInv ==
    \A i, j \in CommittedRwIdx :
        \/ IsPrefix(history[i].observed, history[j].observed)
        \/ IsPrefix(history[j].observed, history[i].observed)

InvalidNotObservedInv ==
    \A i \in InvalidRwIdx :
        \A j \in ResponseIdx :
            history[i].tx \notin Range(history[j].observed)

InvalidNotObservedByCommittedInv ==
    \A i \in InvalidRwIdx :
        \A j \in CommittedRwIdx :
            history[i].tx \notin Range(history[j].observed)

AtMostOnceObservedInv ==
    \A i \in ResponseIdx :
        \A a, b \in DOMAIN history[i].observed :
            (a # b) => history[i].observed[a] # history[i].observed[b]

=============================================================================