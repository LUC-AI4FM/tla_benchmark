---------------------------- MODULE MCMultiNodeReadsAlt ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS HistoryLimit, ViewLimit

CONSTANTS RwTxRequest, RwTxResponse, RoTxRequest, RoTxResponse, TxStatusReceived

CONSTANTS CommittedStatus, InvalidStatus

VARIABLES history, ledgerBranches

vars == << history, ledgerBranches >>

FirstBranch == 1

----------------------------------------------------------------------------------
\* Helpers over the external history

RequestTypes  == {RwTxRequest, RoTxRequest}
ResponseTypes == {RwTxResponse, RoTxResponse}

Requests     == {i \in DOMAIN history : history[i].type \in RequestTypes}
Responses    == {i \in DOMAIN history : history[i].type \in ResponseTypes}
RwResponses  == {i \in DOMAIN history : history[i].type = RwTxResponse}
StatusEvents == {i \in DOMAIN history : history[i].type = TxStatusReceived}

NextRequestId == Cardinality(Requests)

HasResponse(t) == \E i \in Responses : history[i].tx = t

HasStatus(id) == \E i \in StatusEvents : history[i].tx_id = id

IsCommitted(i) ==
    \E j \in StatusEvents :
        /\ history[j].tx_id = history[i].tx_id
        /\ history[j].status = CommittedStatus

IsInvalid(i) ==
    \E j \in StatusEvents :
        /\ history[j].tx_id = history[i].tx_id
        /\ history[j].status = InvalidStatus

CommittedRwResponses == {i \in RwResponses : IsCommitted(i)}
CommittedResponses   == {i \in Responses : IsCommitted(i)}
InvalidRwResponses   == {i \in RwResponses : IsInvalid(i)}

Contains(seq, x) == \E k \in DOMAIN seq : seq[k] = x

IsPrefix(s, t) == Len(s) <= Len(t) /\ SubSeq(t, 1, Len(s)) = s

----------------------------------------------------------------------------------
\* Helpers over the internal ledger branches

LatestBranch == ledgerBranches[Len(ledgerBranches)]

InAnyBranch(t) ==
    \E b \in DOMAIN ledgerBranches :
        \E k \in DOMAIN ledgerBranches[b] : ledgerBranches[b][k].tx = t

InLatest(id) ==
    /\ Len(LatestBranch) >= id[2]
    /\ LatestBranch[id[2]].view = id[1]

ObservedAt(branch, s) == [k \in 1..s |-> branch[k].tx]

----------------------------------------------------------------------------------
\* Initial states

Init ==
    /\ history = << >>
    /\ ledgerBranches = [x \in 1..FirstBranch |-> << >>]

InitAlt ==
    /\ ledgerBranches = <<
            << [view |-> 1, tx |-> 0] >>,
            << [view |-> 1, tx |-> 0], [view |-> 2, tx |-> 1] >>
       >>
    /\ history = <<
            [type |-> RwTxRequest, tx |-> 0],
            [type |-> RwTxResponse, tx |-> 0, observed |-> <<0>>, tx_id |-> <<1, 1>>],
            [type |-> TxStatusReceived, tx_id |-> <<1, 1>>, status |-> CommittedStatus],
            [type |-> RwTxRequest, tx |-> 1],
            [type |-> RwTxResponse, tx |-> 1, observed |-> <<0, 1>>, tx_id |-> <<2, 2>>],
            [type |-> TxStatusReceived, tx_id |-> <<2, 2>>, status |-> CommittedStatus]
       >>

----------------------------------------------------------------------------------
\* Actions

RwTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> NextRequestId])
    /\ UNCHANGED ledgerBranches

RoTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ history' = Append(history, [type |-> RoTxRequest, tx |-> NextRequestId])
    /\ UNCHANGED ledgerBranches

\* The leader of the current view executes a pending read-write request
RwTxExecuteAction ==
    /\ \E i \in Requests :
        /\ history[i].type = RwTxRequest
        /\ ~InAnyBranch(history[i].tx)
        /\ ledgerBranches' =
             [ledgerBranches EXCEPT ![Len(ledgerBranches)] =
                Append(@, [view |-> Len(ledgerBranches), tx |-> history[i].tx])]
    /\ UNCHANGED history

\* A node holding the executed entry replies to the client
RwTxResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E b \in DOMAIN ledgerBranches :
        \E s \in DOMAIN ledgerBranches[b] :
            LET t == ledgerBranches[b][s].tx
            IN /\ ~HasResponse(t)
               /\ history' = Append(history,
                    [type |-> RwTxResponse,
                     tx |-> t,
                     observed |-> ObservedAt(ledgerBranches[b], s),
                     tx_id |-> << ledgerBranches[b][s].view, s >>])
    /\ UNCHANGED ledgerBranches

\* Any node (leader or follower) may serve a read-only request at some ledger point
RoTxResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in Requests :
        /\ history[i].type = RoTxRequest
        /\ ~HasResponse(history[i].tx)
        /\ \E b \in DOMAIN ledgerBranches :
            \E s \in DOMAIN ledgerBranches[b] :
                history' = Append(history,
                    [type |-> RoTxResponse,
                     tx |-> history[i].tx,
                     observed |-> ObservedAt(ledgerBranches[b], s),
                     tx_id |-> << ledgerBranches[b][s].view, s >>])
    /\ UNCHANGED ledgerBranches

StatusCommittedResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in Responses :
        /\ ~HasStatus(history[i].tx_id)
        /\ InLatest(history[i].tx_id)
        /\ history' = Append(history,
             [type |-> TxStatusReceived,
              tx_id |-> history[i].tx_id,
              status |-> CommittedStatus])
    /\ UNCHANGED ledgerBranches

StatusInvalidResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in Responses :
        /\ ~HasStatus(history[i].tx_id)
        /\ ~InLatest(history[i].tx_id)
        /\ history' = Append(history,
             [type |-> TxStatusReceived,
              tx_id |-> history[i].tx_id,
              status |-> InvalidStatus])
    /\ UNCHANGED ledgerBranches

\* A new leader is elected; its ledger is a prefix of the latest branch
\* that retains every committed transaction
TruncateLedgerAction ==
    /\ Len(ledgerBranches) < ViewLimit
    /\ \E l \in 0..Len(LatestBranch) :
        /\ \A i \in StatusEvents :
              history[i].status = CommittedStatus => l >= history[i].tx_id[2]
        /\ ledgerBranches' = Append(ledgerBranches, SubSeq(LatestBranch, 1, l))
    /\ UNCHANGED history

MCNextMultiNodeReadsAction ==
    \/ RwTxRequestAction
    \/ RoTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ RoTxResponseAction
    \/ StatusCommittedResponseAction
    \/ StatusInvalidResponseAction
    \/ TruncateLedgerAction

MCSpecMultiNodeReads == Init /\ [][MCNextMultiNodeReadsAction]_vars

MCSpecMultiNodeReadsAlt == InitAlt /\ [][MCNextMultiNodeReadsAction]_vars

----------------------------------------------------------------------------------
\* Invariants

\* Every response is preceded by the request it answers
AllReceivedIsFirstSentInv ==
    \A i \in Responses :
        \E j \in Requests : j < i /\ history[j].tx = history[i].tx

\* Committed rw txs are observed by every committed tx at a later or equal seqnum
AllCommittedObservedInv ==
    \A i \in CommittedRwResponses :
        \A j \in CommittedResponses :
            history[i].tx_id[2] <= history[j].tx_id[2]
                => Contains(history[j].observed, history[i].tx)

\* Responses only observe transactions that were previously requested
OnlyObserveSentRequestsInv ==
    \A i \in Responses :
        \A k \in DOMAIN history[i].observed :
            \E j \in Requests :
                /\ j < i
                /\ history[j].tx = history[i].observed[k]

\* Each transaction receives at most one response
UniqueTxsInv ==
    \A i, j \in Responses :
        history[i].tx = history[j].tx => i = j

\* Responses with the same transaction id report the same observations
SameObservationsInv ==
    \A i, j \in Responses :
        history[i].tx_id = history[j].tx_id
            => history[i].observed = history[j].observed

\* Distinct read-write transactions have distinct transaction ids
UniqueTxIdsInv ==
    \A i, j \in RwResponses :
        history[i].tx_id = history[j].tx_id => history[i].tx = history[j].tx

\* Each transaction is requested at most once
UniqueTxRequestsInv ==
    \A i, j \in Requests :
        history[i].tx = history[j].tx => i = j

\* Committed read-write transactions have unique sequence numbers
UniqueSeqNumsCommittedInv ==
    \A i, j \in CommittedRwResponses :
        history[i].tx_id[2] = history[j].tx_id[2] => history[i].tx = history[j].tx

\* No transaction id is both committed and invalid
CommittedOrInvalidStrongInv ==
    \A i, j \in StatusEvents :
        history[i].tx_id = history[j].tx_id
            => history[i].status = history[j].status

\* Committed read-write transactions are serializable
CommittedRwSerializableInv ==
    /\ \A i \in CommittedRwResponses :
          /\ Len(history[i].observed) = history[i].tx_id[2]
          /\ history[i].observed[Len(history[i].observed)] = history[i].tx
    /\ \A i, j \in CommittedRwResponses :
          Len(history[i].observed) <= Len(history[j].observed)
              => IsPrefix(history[i].observed, history[j].observed)

\* Invalidated read-write transactions are never observed by committed ones
InvalidNotObservedByCommittedInv ==
    \A i \in InvalidRwResponses :
        \A j \in CommittedResponses :
            ~Contains(history[j].observed, history[i].tx)

\* No transaction is observed more than once in any response
AtMostOnceObservedInv ==
    \A i \in Responses :
        \A k, l \in DOMAIN history[i].observed :
            history[i].observed[k] = history[i].observed[l] => k = l

==================================================================================