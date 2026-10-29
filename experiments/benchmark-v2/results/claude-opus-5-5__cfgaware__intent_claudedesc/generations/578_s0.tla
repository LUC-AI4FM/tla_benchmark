---------------------------- MODULE MCMultiNodeReads ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS RwTxRequest, RwTxResponse, RoTxRequest, RoTxResponse, TxStatusReceived
CONSTANTS CommittedStatus, InvalidStatus
CONSTANTS FirstBranch, HistoryLimit, ViewLimit

VARIABLES history, ledgerBranches, commitSeqNum

vars == <<history, ledgerBranches, commitSeqNum>>

TxStatuses == {CommittedStatus, InvalidStatus}

----------------------------------------------------------------------------
\* Helpers

Latest == ledgerBranches[Len(ledgerBranches)]

TxsIn(s) == [k \in 1..Len(s) |-> s[k].tx]

Contains(s, x) == \E k \in DOMAIN s : s[k] = x

IsPrefix(s, t) == Len(s) <= Len(t) /\ SubSeq(t, 1, Len(s)) = s

IsReq(i)  == history[i].type \in {RwTxRequest, RoTxRequest}
IsResp(i) == history[i].type \in {RwTxResponse, RoTxResponse}
IsRwResp(i) == history[i].type = RwTxResponse

ReqTypeOf(t) == IF t = RwTxResponse THEN RwTxRequest ELSE RoTxRequest

InAnyBranch(tx) ==
    \E w \in DOMAIN ledgerBranches :
        \E k \in DOMAIN ledgerBranches[w] : ledgerBranches[w][k].tx = tx

Responded(tx) ==
    \E j \in DOMAIN history : IsResp(j) /\ history[j].tx = tx

CommittedTxIds ==
    { history[i].tx_id : i \in { j \in DOMAIN history :
        history[j].type = TxStatusReceived /\ history[j].status = CommittedStatus } }

InvalidTxIds ==
    { history[i].tx_id : i \in { j \in DOMAIN history :
        history[j].type = TxStatusReceived /\ history[j].status = InvalidStatus } }

CommittedRw ==
    { i \in DOMAIN history : IsRwResp(i) /\ history[i].tx_id \in CommittedTxIds }

InvalidRw ==
    { i \in DOMAIN history : IsRwResp(i) /\ history[i].tx_id \in InvalidTxIds }

----------------------------------------------------------------------------
\* Initial state

Init ==
    /\ history = <<>>
    /\ ledgerBranches = [x \in 1..FirstBranch |-> <<>>]
    /\ commitSeqNum = 0

----------------------------------------------------------------------------
\* Multi-node actions (read-write transactions, replication, view changes)

RwTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> Len(history) + 1])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

RwTxExecuteAction ==
    \E v \in DOMAIN ledgerBranches, i \in DOMAIN history :
        /\ history[i].type = RwTxRequest
        /\ ~InAnyBranch(history[i].tx)
        /\ ledgerBranches' = [ledgerBranches EXCEPT ![v] =
                                Append(@, [view |-> v, tx |-> history[i].tx])]
        /\ UNCHANGED <<history, commitSeqNum>>

RwTxResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E v \in DOMAIN ledgerBranches :
         \E k \in DOMAIN ledgerBranches[v] :
            LET e == ledgerBranches[v][k] IN
            /\ e.view = v
            /\ ~Responded(e.tx)
            /\ history' = Append(history,
                    [type     |-> RwTxResponse,
                     tx       |-> e.tx,
                     observed |-> TxsIn(SubSeq(ledgerBranches[v], 1, k)),
                     tx_id    |-> <<v, k>>])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

IncreaseCommitAction ==
    \E c \in (commitSeqNum + 1)..Len(Latest) :
        /\ commitSeqNum' = c
        /\ UNCHANGED <<history, ledgerBranches>>

TruncateLedgerAction ==
    /\ Len(ledgerBranches) < ViewLimit
    /\ \E v \in DOMAIN ledgerBranches :
         \E k \in commitSeqNum..Len(ledgerBranches[v]) :
            /\ SubSeq(ledgerBranches[v], 1, commitSeqNum) = SubSeq(Latest, 1, commitSeqNum)
            /\ ledgerBranches' = Append(ledgerBranches, SubSeq(ledgerBranches[v], 1, k))
    /\ UNCHANGED <<history, commitSeqNum>>

StatusCommittedResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN history :
         /\ IsRwResp(i)
         /\ LET t == history[i].tx_id IN
            /\ t[2] <= commitSeqNum
            /\ Latest[t[2]].view = t[1]
            /\ history' = Append(history,
                    [type |-> TxStatusReceived, tx_id |-> t, status |-> CommittedStatus])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

StatusInvalidResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN history :
         /\ IsRwResp(i)
         /\ LET t == history[i].tx_id IN
            /\ t[2] <= commitSeqNum
            /\ Latest[t[2]].view # t[1]
            /\ history' = Append(history,
                    [type |-> TxStatusReceived, tx_id |-> t, status |-> InvalidStatus])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

NextMultiNodeAction ==
    \/ RwTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ IncreaseCommitAction
    \/ TruncateLedgerAction
    \/ StatusCommittedResponseAction
    \/ StatusInvalidResponseAction

----------------------------------------------------------------------------
\* Read-only transactions

RoTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ history' = Append(history, [type |-> RoTxRequest, tx |-> Len(history) + 1])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

RoTxResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN history, v \in DOMAIN ledgerBranches :
         /\ history[i].type = RoTxRequest
         /\ ~Responded(history[i].tx)
         /\ Len(ledgerBranches[v]) > 0
         /\ LET b == ledgerBranches[v]
                k == Len(b)
            IN history' = Append(history,
                    [type     |-> RoTxResponse,
                     tx       |-> history[i].tx,
                     observed |-> TxsIn(b),
                     tx_id    |-> <<b[k].view, k>>])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

NextMultiNodeReadsAction ==
    \/ NextMultiNodeAction
    \/ RoTxRequestAction
    \/ RoTxResponseAction

MCSpecMultiNodeReads == Init /\ [][NextMultiNodeReadsAction]_vars

----------------------------------------------------------------------------
\* Invariants

AllReceivedIsFirstSentInv ==
    \A i \in DOMAIN history :
        IsResp(i) =>
            \E j \in 1..(i - 1) :
                /\ history[j].type = ReqTypeOf(history[i].type)
                /\ history[j].tx = history[i].tx

AllCommittedObservedInv ==
    \A i, j \in CommittedRw :
        history[i].tx_id[2] < history[j].tx_id[2]
            => Contains(history[j].observed, history[i].tx)

OnlyObserveSentRequestsInv ==
    \A i \in DOMAIN history :
        IsResp(i) =>
            \A k \in DOMAIN history[i].observed :
                \E j \in DOMAIN history :
                    /\ history[j].type = RwTxRequest
                    /\ history[j].tx = history[i].observed[k]

UniqueTxsInv ==
    \A i, j \in DOMAIN history :
        (IsResp(i) /\ IsResp(j) /\ history[i].tx = history[j].tx) => i = j

SameObservationsInv ==
    \A i, j \in DOMAIN history :
        (IsResp(i) /\ IsResp(j) /\ history[i].tx_id = history[j].tx_id)
            => history[i].observed = history[j].observed

UniqueTxIdsInv ==
    \A i, j \in DOMAIN history :
        (IsRwResp(i) /\ IsRwResp(j) /\ history[i].tx_id = history[j].tx_id) => i = j

UniqueTxRequestsInv ==
    \A i, j \in DOMAIN history :
        (IsReq(i) /\ IsReq(j) /\ history[i].tx = history[j].tx) => i = j

UniqueSeqNumsCommittedInv ==
    \A i, j \in CommittedRw :
        history[i].tx_id[2] = history[j].tx_id[2] => i = j

CommittedOrInvalidStrongInv ==
    CommittedTxIds \cap InvalidTxIds = {}

CommittedRwSerializableInv ==
    \A i, j \in CommittedRw :
        \/ IsPrefix(history[i].observed, history[j].observed)
        \/ IsPrefix(history[j].observed, history[i].observed)

InvalidNotObservedByCommittedInv ==
    \A i \in InvalidRw, j \in CommittedRw :
        ~Contains(history[j].observed, history[i].tx)

AtMostOnceObservedInv ==
    \A i \in DOMAIN history :
        IsResp(i) =>
            \A a, b \in DOMAIN history[i].observed :
                history[i].observed[a] = history[i].observed[b] => a = b

CommittedRwOrderedSpecLinearizableInv ==
    \A i, j \in CommittedRw :
        (\E r \in DOMAIN history :
            /\ i < r
            /\ history[r].type = RwTxRequest
            /\ history[r].tx = history[j].tx)
        => history[i].tx_id[2] < history[j].tx_id[2]

=============================================================================