---------------------------- MODULE SingleNodeReads ----------------------------
\* Self-contained model of read-only transactions on a single-node system.
\* The SingleNode base model (rw requests, execution, responses, signatures,
\* commit, view changes/truncation, status responses) is inlined so that the
\* module parses standalone. The extension adds RoTxRequestAction and
\* RoTxResponseAction. It assumes read-only transactions are always forwarded,
\* and that the read and the response happen in one atomic step.

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS HistoryLimit, ViewLimit

ASSUME HistoryLimit \in Nat /\ ViewLimit \in Nat \ {0}

\* Event types in the external history
RwTxRequest      == "RwTxRequest"
RwTxResponse     == "RwTxResponse"
RoTxRequest      == "RoTxRequest"
RoTxResponse     == "RoTxResponse"
TxStatusReceived == "TxStatusReceived"

\* Transaction statuses
CommittedStatus == "CommittedStatus"
InvalidStatus   == "InvalidStatus"

\* Marker for ledger entries that are not client transactions (e.g. signatures)
NoTx == 0

Views == 1..ViewLimit
TxIds == 1..HistoryLimit

VARIABLES
    history,         \* sequence of client-observable events
    ledgerBranches,  \* sequence of ledger branches, one per view
    commitSeqnum     \* highest committed sequence number

vars == <<history, ledgerBranches, commitSeqnum>>

-----------------------------------------------------------------------------
\* Helpers

CurrentView == Len(ledgerBranches)

Latest == ledgerBranches[CurrentView]

NextRequestId == Len(history) + 1

\* Client transaction ids observed in branch up to and including index i
ObservedTxs(branch, i) ==
    LET p == SelectSeq(SubSeq(branch, 1, i), LAMBDA e : e.tx # NoTx)
    IN  [j \in DOMAIN p |-> p[j].tx]

TxInLatest(t) == \E k \in DOMAIN Latest : Latest[k].tx = t

HasResponse(type, t) ==
    \E k \in DOMAIN history : history[k].type = type /\ history[k].tx = t

HasStatus(txid) ==
    \E k \in DOMAIN history :
        /\ history[k].type = TxStatusReceived
        /\ history[k].tx_id = txid

-----------------------------------------------------------------------------
\* Type invariant

Entries == [view : Views, tx : TxIds \cup {NoTx}]

TypeOK ==
    /\ history \in Seq([type : {RwTxRequest, RwTxResponse, RoTxRequest,
                                RoTxResponse, TxStatusReceived}] \cup
                       {e \in UNION {[type : {RwTxRequest, RwTxResponse,
                                              RoTxRequest, RoTxResponse,
                                              TxStatusReceived}]} : TRUE}
                       \cup {e : e \in {}})
       \/ \A k \in DOMAIN history :
            history[k].type \in {RwTxRequest, RwTxResponse, RoTxRequest,
                                 RoTxResponse, TxStatusReceived}
    /\ ledgerBranches \in Seq(Seq(Entries))
    /\ Len(ledgerBranches) \in Views
    /\ commitSeqnum \in Nat
    /\ commitSeqnum <= Len(Latest)

-----------------------------------------------------------------------------
\* Initial state

Init ==
    /\ history = <<>>
    /\ ledgerBranches = << <<>> >>
    /\ commitSeqnum = 0

-----------------------------------------------------------------------------
\* SingleNode actions

\* Client submits a new read-write transaction
RwTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> NextRequestId])
    /\ UNCHANGED <<ledgerBranches, commitSeqnum>>

\* Node executes a read-write transaction, appending it to the current branch
RwTxExecuteAction ==
    /\ Len(Latest) < HistoryLimit
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxRequest
        /\ ~TxInLatest(history[i].tx)
        /\ ledgerBranches' =
             [ledgerBranches EXCEPT ![CurrentView] =
                 Append(@, [view |-> CurrentView, tx |-> history[i].tx])]
    /\ UNCHANGED <<history, commitSeqnum>>

\* Node responds to an executed read-write transaction
RwTxResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN Latest :
        /\ Latest[i].tx # NoTx
        /\ ~HasResponse(RwTxResponse, Latest[i].tx)
        /\ history' = Append(history,
                         [type     |-> RwTxResponse,
                          tx       |-> Latest[i].tx,
                          observed |-> ObservedTxs(Latest, i),
                          tx_id    |-> <<Latest[i].view, i>>])
    /\ UNCHANGED <<ledgerBranches, commitSeqnum>>

\* Node appends a non-client entry (e.g. signature) to the current branch
AppendOtherTxnAction ==
    /\ Len(Latest) < HistoryLimit
    /\ ledgerBranches' =
         [ledgerBranches EXCEPT ![CurrentView] =
             Append(@, [view |-> CurrentView, tx |-> NoTx])]
    /\ UNCHANGED <<history, commitSeqnum>>

\* Node commits a prefix of the current branch
CommitAction ==
    /\ \E i \in (commitSeqnum + 1)..Len(Latest) :
        commitSeqnum' = i
    /\ UNCHANGED <<history, ledgerBranches>>

\* Node starts a new view, keeping a prefix of the current branch that
\* includes at least everything committed
TruncateLedgerAction ==
    /\ Len(ledgerBranches) < ViewLimit
    /\ \E i \in commitSeqnum..Len(Latest) :
        ledgerBranches' = Append(ledgerBranches, SubSeq(Latest, 1, i))
    /\ UNCHANGED <<history, commitSeqnum>>

\* Client learns that a transaction is committed
StatusCommittedResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        /\ ~HasStatus(history[i].tx_id)
        /\ history[i].tx_id[2] <= commitSeqnum
        /\ Latest[history[i].tx_id[2]].view = history[i].tx_id[1]
        /\ history' = Append(history,
                         [type   |-> TxStatusReceived,
                          tx_id  |-> history[i].tx_id,
                          status |-> CommittedStatus])
    /\ UNCHANGED <<ledgerBranches, commitSeqnum>>

\* Client learns that a transaction is invalid
StatusInvalidResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        /\ ~HasStatus(history[i].tx_id)
        /\ history[i].tx_id[2] <= commitSeqnum
        /\ Latest[history[i].tx_id[2]].view # history[i].tx_id[1]
        /\ history' = Append(history,
                         [type   |-> TxStatusReceived,
                          tx_id  |-> history[i].tx_id,
                          status |-> InvalidStatus])
    /\ UNCHANGED <<ledgerBranches, commitSeqnum>>

NextSingleNodeAction ==
    \/ RwTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ AppendOtherTxnAction
    \/ CommitAction
    \/ TruncateLedgerAction
    \/ StatusCommittedResponseAction
    \/ StatusInvalidResponseAction

-----------------------------------------------------------------------------
\* Read-only extension

\* Client submits a new read-only transaction
RoTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ history' = Append(history, [type |-> RoTxRequest, tx |-> NextRequestId])
    /\ UNCHANGED <<ledgerBranches, commitSeqnum>>

\* Node executes a read-only transaction and responds in one atomic step.
\* Read-only transactions are assumed to always be forwarded, so the response
\* may observe the contents of any (non-empty) ledger branch.
RoTxResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RoTxRequest
        /\ ~HasResponse(RoTxResponse, history[i].tx)
        /\ \E view \in DOMAIN ledgerBranches :
            LET branch == ledgerBranches[view]
                n      == Len(branch)
            IN  /\ n > 0
                /\ history' = Append(history,
                                 [type     |-> RoTxResponse,
                                  tx       |-> history[i].tx,
                                  observed |-> ObservedTxs(branch, n),
                                  tx_id    |-> <<branch[n].view, n>>])
    /\ UNCHANGED <<ledgerBranches, commitSeqnum>>

NextSingleNodeReadsAction ==
    \/ NextSingleNodeAction
    \/ RoTxRequestAction
    \/ RoTxResponseAction

SpecSingleNodeReads == Init /\ [][NextSingleNodeReadsAction]_vars

Spec == SpecSingleNodeReads

-----------------------------------------------------------------------------
\* Safety invariants

\* Each request receives at most one response
AtMostOneResponseInv ==
    \A i, j \in DOMAIN history :
        /\ history[i].type \in {RwTxResponse, RoTxResponse}
        /\ history[j].type = history[i].type
        /\ history[i].tx = history[j].tx
        => i = j

\* No transaction id is reported both committed and invalid
CommittedOrInvalidInv ==
    \A i, j \in DOMAIN history :
        /\ history[i].type = TxStatusReceived
        /\ history[j].type = TxStatusReceived
        /\ history[i].tx_id = history[j].tx_id
        => history[i].status = history[j].status

\* Committed entries of the current branch are never lost on view change
CommittedPrefixInv ==
    \A v \in DOMAIN ledgerBranches :
        v >= 1 /\ Len(ledgerBranches[v]) >= commitSeqnum /\ v = CurrentView
        => SubSeq(ledgerBranches[v], 1, commitSeqnum) =
           SubSeq(Latest, 1, commitSeqnum)

\* Every response corresponds to an earlier request of the matching kind
ResponseFollowsRequestInv ==
    \A i \in DOMAIN history :
        /\ (history[i].type = RwTxResponse =>
              \E j \in 1..(i - 1) :
                  history[j].type = RwTxRequest /\ history[j].tx = history[i].tx)
        /\ (history[i].type = RoTxResponse =>
              \E j \in 1..(i - 1) :
                  history[j].type = RoTxRequest /\ history[j].tx = history[i].tx)

=============================================================================