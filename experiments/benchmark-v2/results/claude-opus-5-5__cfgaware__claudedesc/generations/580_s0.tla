---- MODULE MCSingleNodeReads ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS RwTxRequest, RwTxResponse, RoTxRequest, RoTxResponse, TxStatusReceived
CONSTANTS CommittedStatus, InvalidStatus
CONSTANTS FirstBranch, HistoryLimit

VARIABLES history, ledger

vars == <<history, ledger>>

ResponseTypes == {RwTxResponse, RoTxResponse}

----------------------------------------------------------------------------
\* Helpers

IsPrefix(s, t) == Len(s) <= Len(t) /\ SubSeq(t, 1, Len(s)) = s

InSeq(x, s) == \E n \in DOMAIN s : s[n] = x

Executed(tx) == \E k \in DOMAIN ledger : ledger[k].tx = tx

Responded(tx) ==
    \E k \in DOMAIN history :
        /\ history[k].type \in ResponseTypes
        /\ history[k].tx = tx

HasStatus(tid) ==
    \E k \in DOMAIN history :
        /\ history[k].type = TxStatusReceived
        /\ history[k].tx_id = tid

IsCommittedResp(k) ==
    /\ history[k].type = RwTxResponse
    /\ \E s \in DOMAIN history :
        /\ history[s].type = TxStatusReceived
        /\ history[s].tx_id = history[k].tx_id
        /\ history[s].status = CommittedStatus

----------------------------------------------------------------------------
\* Single node behaviour

Init ==
    /\ history = <<>>
    /\ ledger = <<>>

RwTxRequestAction ==
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> Len(history) + 1])
    /\ UNCHANGED ledger

RwTxExecuteAction ==
    \E i \in DOMAIN history :
        /\ history[i].type = RwTxRequest
        /\ ~Executed(history[i].tx)
        /\ (\A j \in 1..(i-1) :
                (history[j].type = RwTxRequest) => Executed(history[j].tx))
        /\ ledger' = Append(ledger, [view |-> FirstBranch, tx |-> history[i].tx])
        /\ UNCHANGED history

RwTxResponseAction ==
    \E j \in DOMAIN ledger :
        /\ ~Responded(ledger[j].tx)
        /\ history' = Append(history,
                [type |-> RwTxResponse,
                 tx |-> ledger[j].tx,
                 observed |-> [k \in 1..j |-> ledger[k].tx],
                 tx_id |-> <<ledger[j].view, j>>])
        /\ UNCHANGED ledger

StatusCommittedResponseAction ==
    \E i \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        /\ ~HasStatus(history[i].tx_id)
        /\ history[i].tx_id[2] <= Len(ledger)
        /\ history' = Append(history,
                [type |-> TxStatusReceived,
                 tx_id |-> history[i].tx_id,
                 status |-> CommittedStatus])
        /\ UNCHANGED ledger

\* Read-only transactions

RoTxRequestAction ==
    /\ history' = Append(history, [type |-> RoTxRequest, tx |-> Len(history) + 1])
    /\ UNCHANGED ledger

RoTxResponseAction ==
    \E i \in DOMAIN history :
        /\ history[i].type = RoTxRequest
        /\ ~Responded(history[i].tx)
        /\ history' = Append(history,
                [type |-> RoTxResponse,
                 tx |-> history[i].tx,
                 observed |-> [k \in 1..Len(ledger) |-> ledger[k].tx],
                 tx_id |-> <<FirstBranch, Len(ledger)>>])
        /\ UNCHANGED ledger

----------------------------------------------------------------------------
\* Bounded actions

MCRwTxRequestAction == Len(history) < HistoryLimit /\ RwTxRequestAction
MCRwTxResponseAction == Len(history) < HistoryLimit /\ RwTxResponseAction
MCStatusCommittedResponseAction == Len(history) < HistoryLimit /\ StatusCommittedResponseAction
MCRoTxRequestAction == Len(history) < HistoryLimit /\ RoTxRequestAction
MCRoTxResponseAction == Len(history) < HistoryLimit /\ RoTxResponseAction

MCNextSingleNode ==
    \/ MCRwTxRequestAction
    \/ RwTxExecuteAction
    \/ MCRwTxResponseAction
    \/ MCStatusCommittedResponseAction

MCNextSingleNodeReads ==
    \/ MCNextSingleNode
    \/ MCRoTxRequestAction
    \/ MCRoTxResponseAction

MCSpecSingleNodeReads == Init /\ [][MCNextSingleNodeReads]_vars

----------------------------------------------------------------------------
\* Invariants

AllReceivedIsFirstSentInv ==
    \A i, j \in DOMAIN history :
        ( /\ history[i].type = RwTxResponse
          /\ history[j].type = RwTxRequest
          /\ \A m \in 1..(j-1) : history[m].type # RwTxRequest )
        => history[i].observed[1] = history[j].tx

AllCommittedObservedInv ==
    \A i, j, k \in DOMAIN history :
        ( /\ history[i].type = TxStatusReceived
          /\ history[i].status = CommittedStatus
          /\ history[k].type = RwTxResponse
          /\ history[k].tx_id = history[i].tx_id
          /\ history[j].type = RwTxResponse
          /\ i < history[j].tx )
        => InSeq(history[k].tx, history[j].observed)

AllCommittedObservedRoInv ==
    \A i, j, k \in DOMAIN history :
        ( /\ history[i].type = TxStatusReceived
          /\ history[i].status = CommittedStatus
          /\ history[k].type = RwTxResponse
          /\ history[k].tx_id = history[i].tx_id
          /\ history[j].type = RoTxResponse
          /\ i < history[j].tx )
        => InSeq(history[k].tx, history[j].observed)

OnlyObserveSentRequestsInv ==
    \A i \in DOMAIN history :
        (history[i].type \in ResponseTypes) =>
            \A n \in DOMAIN history[i].observed :
                \E j \in 1..(i-1) :
                    /\ history[j].type = RwTxRequest
                    /\ history[j].tx = history[i].observed[n]

UniqueTxsInv ==
    \A i, j \in DOMAIN history :
        ( /\ i # j
          /\ history[i].type \in ResponseTypes
          /\ history[j].type \in ResponseTypes )
        => history[i].tx # history[j].tx

UniqueTxIdsInv ==
    \A i, j \in DOMAIN history :
        ( /\ i # j
          /\ history[i].type = RwTxResponse
          /\ history[j].type = RwTxResponse )
        => history[i].tx_id # history[j].tx_id

UniqueSeqNumsInv ==
    \A i, j \in DOMAIN history :
        ( /\ i # j
          /\ history[i].type = RwTxResponse
          /\ history[j].type = RwTxResponse )
        => history[i].tx_id[2] # history[j].tx_id[2]

CommittedOrInvalidStrongInv ==
    \A i \in DOMAIN history :
        (history[i].type = TxStatusReceived) =>
            /\ history[i].status \in {CommittedStatus, InvalidStatus}
            /\ \E k \in 1..(i-1) :
                 /\ history[k].type = RwTxResponse
                 /\ history[k].tx_id = history[i].tx_id
            /\ \A j \in DOMAIN history :
                 ( /\ history[j].type = TxStatusReceived
                   /\ history[j].tx_id = history[i].tx_id )
                 => history[j].status = history[i].status

RwSerializableInv ==
    \A i, j \in DOMAIN history :
        ( /\ history[i].type = RwTxResponse
          /\ history[j].type = RwTxResponse )
        => \/ IsPrefix(history[i].observed, history[j].observed)
           \/ IsPrefix(history[j].observed, history[i].observed)

CommittedRwSerializableInv ==
    \A i, j \in DOMAIN history :
        ( /\ IsCommittedResp(i)
          /\ IsCommittedResp(j) )
        => \/ IsPrefix(history[i].observed, history[j].observed)
           \/ IsPrefix(history[j].observed, history[i].observed)

InvalidNotObservedInv ==
    \A i, j, k \in DOMAIN history :
        ( /\ history[i].type = TxStatusReceived
          /\ history[i].status = InvalidStatus
          /\ history[k].type = RwTxResponse
          /\ history[k].tx_id = history[i].tx_id
          /\ history[j].type \in ResponseTypes
          /\ j # k )
        => ~InSeq(history[k].tx, history[j].observed)

InvalidNotObservedByCommittedInv ==
    \A i, j, k \in DOMAIN history :
        ( /\ history[i].type = TxStatusReceived
          /\ history[i].status = InvalidStatus
          /\ history[k].type = RwTxResponse
          /\ history[k].tx_id = history[i].tx_id
          /\ IsCommittedResp(j) )
        => ~InSeq(history[k].tx, history[j].observed)

AtMostOnceObservedInv ==
    \A i \in DOMAIN history :
        (history[i].type \in ResponseTypes) =>
            \A a, b \in DOMAIN history[i].observed :
                (a # b) => history[i].observed[a] # history[i].observed[b]

====