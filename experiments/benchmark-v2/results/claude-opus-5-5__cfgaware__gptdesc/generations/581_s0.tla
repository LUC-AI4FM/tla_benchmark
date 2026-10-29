---- MODULE MCSingleNode ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS RwTxRequest, RwTxResponse, RoTxRequest, RoTxResponse, TxStatusReceived
CONSTANTS CommittedStatus, InvalidStatus
CONSTANT FirstBranch
CONSTANT HistoryLimit

VARIABLES history, ledger

vars == << history, ledger >>

\* ---------------------------------------------------------------------
\* Helpers over the history
\* ---------------------------------------------------------------------

Range(s) == { s[k] : k \in DOMAIN s }

IsPrefix(a, b) == Len(a) <= Len(b) /\ SubSeq(b, 1, Len(a)) = a

RwReqIdx    == { i \in DOMAIN history : history[i].type = RwTxRequest }
RoReqIdx    == { i \in DOMAIN history : history[i].type = RoTxRequest }
RwRespIdx   == { i \in DOMAIN history : history[i].type = RwTxResponse }
RoRespIdx   == { i \in DOMAIN history : history[i].type = RoTxResponse }
StatusIdx   == { i \in DOMAIN history : history[i].type = TxStatusReceived }
ReqIdx      == RwReqIdx \cup RoReqIdx
RespIdx     == RwRespIdx \cup RoRespIdx
CommittedIdx == { i \in StatusIdx : history[i].status = CommittedStatus }
InvalidIdx   == { i \in StatusIdx : history[i].status = InvalidStatus }

RequestTypeOf(t) == IF t = RwTxResponse THEN RwTxRequest ELSE RoTxRequest

CommittedRwRespIdx ==
    { r \in RwRespIdx : \E c \in CommittedIdx : history[c].tx_id = history[r].tx_id }

\* ---------------------------------------------------------------------
\* Single node specification
\* ---------------------------------------------------------------------

Init ==
    /\ history = << >>
    /\ ledger = << >>

RwTxRequestAction ==
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> Len(history) + 1])
    /\ UNCHANGED ledger

RwTxExecuteAction ==
    /\ \E i \in RwReqIdx :
        /\ history[i].tx \notin Range(ledger)
        /\ ledger' = Append(ledger, history[i].tx)
    /\ UNCHANGED history

RwTxResponseAction ==
    /\ \E s \in 1..Len(ledger) :
        /\ ~\E r \in RwRespIdx : history[r].tx = ledger[s]
        /\ history' = Append(history,
                [type |-> RwTxResponse,
                 tx |-> ledger[s],
                 observed |-> SubSeq(ledger, 1, s),
                 tx_id |-> << FirstBranch, s >>])
    /\ UNCHANGED ledger

RoTxRequestAction ==
    /\ history' = Append(history, [type |-> RoTxRequest, tx |-> Len(history) + 1])
    /\ UNCHANGED ledger

RoTxResponseAction ==
    /\ \E i \in RoReqIdx :
        /\ ~\E r \in RoRespIdx : history[r].tx = history[i].tx
        /\ history' = Append(history,
                [type |-> RoTxResponse,
                 tx |-> history[i].tx,
                 observed |-> ledger,
                 tx_id |-> << FirstBranch, Len(ledger) >>])
    /\ UNCHANGED ledger

StatusCommittedResponseAction ==
    /\ \E r \in RwRespIdx :
        /\ ~\E k \in StatusIdx : history[k].tx_id = history[r].tx_id
        /\ history' = Append(history,
                [type |-> TxStatusReceived,
                 tx_id |-> history[r].tx_id,
                 status |-> CommittedStatus])
    /\ UNCHANGED ledger

\* ---------------------------------------------------------------------
\* Bounded model-checking wrapper
\* ---------------------------------------------------------------------

MCRwTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ RwTxRequestAction

MCRoTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ RoTxRequestAction

MCSingleNodeNext ==
    \/ MCRwTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ MCRoTxRequestAction
    \/ RoTxResponseAction
    \/ StatusCommittedResponseAction

MCSpecSingleNode == Init /\ [][MCSingleNodeNext]_vars

\* ---------------------------------------------------------------------
\* Invariants
\* ---------------------------------------------------------------------

AllReceivedIsFirstSentInv ==
    \A i \in RespIdx :
        \E j \in 1..(i - 1) :
            /\ history[j].type = RequestTypeOf(history[i].type)
            /\ history[j].tx = history[i].tx

AllCommittedObservedInv ==
    \A c \in CommittedIdx :
        \A j \in RespIdx :
            (\E k \in ReqIdx : k > c /\ k < j /\ history[k].tx = history[j].tx)
            => \A r \in RwRespIdx :
                  history[r].tx_id = history[c].tx_id
                  => history[r].tx \in Range(history[j].observed)

OnlyObserveSentRequestsInv ==
    \A i \in RespIdx :
        \A t \in Range(history[i].observed) :
            \E j \in RwReqIdx : j < i /\ history[j].tx = t

UniqueTxsInv ==
    \A i, j \in ReqIdx : history[i].tx = history[j].tx => i = j

UniqueTxIdsInv ==
    \A i, j \in RwRespIdx : history[i].tx_id = history[j].tx_id => i = j

UniqueSeqNumsInv ==
    \A i, j \in CommittedIdx :
        history[i].tx_id[2] = history[j].tx_id[2] => history[i].tx_id = history[j].tx_id

CommittedOrInvalidStrongInv ==
    \A i \in CommittedIdx, j \in InvalidIdx :
        ~ ( /\ history[j].tx_id[1] = history[i].tx_id[1]
            /\ history[j].tx_id[2] <= history[i].tx_id[2] )

RwSerializableInv ==
    \A i, j \in RwRespIdx :
        IsPrefix(history[i].observed, history[j].observed)
        \/ IsPrefix(history[j].observed, history[i].observed)

CommittedRwSerializableInv ==
    \A i, j \in CommittedRwRespIdx :
        IsPrefix(history[i].observed, history[j].observed)
        \/ IsPrefix(history[j].observed, history[i].observed)

InvalidNotObservedInv ==
    \A v \in InvalidIdx :
        \A r \in RwRespIdx :
            history[r].tx_id = history[v].tx_id
            => \A j \in RespIdx : history[r].tx \notin Range(history[j].observed)

InvalidNotObservedByCommittedInv ==
    \A v \in InvalidIdx :
        \A r \in RwRespIdx :
            history[r].tx_id = history[v].tx_id
            => \A j \in CommittedRwRespIdx : history[r].tx \notin Range(history[j].observed)

AtMostOnceObservedInv ==
    \A i \in RespIdx :
        \A a, b \in DOMAIN history[i].observed :
            history[i].observed[a] = history[i].observed[b] => a = b

====