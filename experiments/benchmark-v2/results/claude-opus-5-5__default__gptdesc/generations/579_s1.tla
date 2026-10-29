---------------------------- MODULE MCMultiNode ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* Bound on the number of views, i.e. the number of view changes plus one
CONSTANT ViewLimit

ASSUME ViewLimit \in Nat /\ ViewLimit >= 1

\* Bound on the length of the client-observed history
HistoryLimit == 8

VARIABLES
    history,         \* sequence of client-observable events
    ledgerBranches   \* sequence of ledgers, one per view

vars == << history, ledgerBranches >>

-----------------------------------------------------------------------------
\* Event types and statuses

RwTxnRequest     == "RwTxnRequest"
RwTxnResponse    == "RwTxnResponse"
TxStatusReceived == "TxStatusReceived"

CommittedStatus == "CommittedStatus"
InvalidStatus   == "InvalidStatus"

-----------------------------------------------------------------------------
\* Helpers

Max(S) == CHOOSE x \in S : \A y \in S : y <= x

CurrentView == Len(ledgerBranches)

Ledger == ledgerBranches[CurrentView]

NextTxId ==
    Cardinality({ i \in DOMAIN history : history[i].type = RwTxnRequest }) + 1

StatusReceived(txid) ==
    \E j \in DOMAIN history :
        /\ history[j].type = TxStatusReceived
        /\ history[j].tx_id = txid

HasStatus(txid, st) ==
    \E j \in DOMAIN history :
        /\ history[j].type = TxStatusReceived
        /\ history[j].tx_id = txid
        /\ history[j].status = st

CommittedSeqnos ==
    { history[j].tx_id[2] :
        j \in { k \in DOMAIN history :
                  /\ history[k].type = TxStatusReceived
                  /\ history[k].status = CommittedStatus } }

CommitIndex ==
    IF CommittedSeqnos = {} THEN 0 ELSE Max(CommittedSeqnos)

-----------------------------------------------------------------------------
\* Base MultiNode behaviour

Init ==
    /\ history = << >>
    /\ ledgerBranches = << << >> >>

\* A client submits a new read-write transaction
RwTxnRequestAction ==
    /\ history' = Append(history, [type |-> RwTxnRequest, tx |-> NextTxId])
    /\ UNCHANGED ledgerBranches

\* The current primary executes a requested transaction, appending it
\* to the ledger of the current view
RwTxnExecuteAction ==
    /\ \E i \in DOMAIN history :
         /\ history[i].type = RwTxnRequest
         /\ \A k \in DOMAIN Ledger : Ledger[k].tx /= history[i].tx
         /\ ledgerBranches' =
              [ledgerBranches EXCEPT ![CurrentView] =
                  Append(@, [view |-> CurrentView, tx |-> history[i].tx])]
    /\ UNCHANGED history

\* A node replies to the client with the transaction id of an executed txn
RwTxnResponseAction ==
    /\ \E v \in DOMAIN ledgerBranches :
         \E s \in DOMAIN ledgerBranches[v] :
           LET e == ledgerBranches[v][s] IN
           /\ ~\E j \in DOMAIN history :
                  /\ history[j].type = RwTxnResponse
                  /\ history[j].tx = e.tx
           /\ history' = Append(history,
                  [type |-> RwTxnResponse, tx |-> e.tx, tx_id |-> << e.view, s >>])
    /\ UNCHANGED ledgerBranches

\* A transaction that is in the current ledger is reported committed
StatusCommittedResponseAction ==
    /\ \E i \in DOMAIN history :
         /\ history[i].type = RwTxnResponse
         /\ LET v == history[i].tx_id[1]
                s == history[i].tx_id[2]
            IN
            /\ s \in DOMAIN Ledger
            /\ Ledger[s].view = v
            /\ ~StatusReceived(<< v, s >>)
            /\ history' = Append(history,
                   [type |-> TxStatusReceived, tx_id |-> << v, s >>,
                    status |-> CommittedStatus])
    /\ UNCHANGED ledgerBranches

\* A transaction that was rolled back by a view change is reported invalid
StatusInvalidResponseAction ==
    /\ \E i \in DOMAIN history :
         /\ history[i].type = RwTxnResponse
         /\ LET v == history[i].tx_id[1]
                s == history[i].tx_id[2]
            IN
            /\ v < CurrentView
            /\ \/ s \notin DOMAIN Ledger
               \/ Ledger[s].view /= v
            /\ ~StatusReceived(<< v, s >>)
            /\ history' = Append(history,
                   [type |-> TxStatusReceived, tx_id |-> << v, s >>,
                    status |-> InvalidStatus])
    /\ UNCHANGED ledgerBranches

\* A view change: a new branch is started from a prefix of the current
\* ledger that retains at least all committed entries
TruncateLedgerAction ==
    /\ \E i \in CommitIndex..Len(Ledger) :
         ledgerBranches' = Append(ledgerBranches, SubSeq(Ledger, 1, i))
    /\ UNCHANGED history

NextMultiNodeAction ==
    \/ RwTxnRequestAction
    \/ RwTxnExecuteAction
    \/ RwTxnResponseAction
    \/ StatusCommittedResponseAction
    \/ StatusInvalidResponseAction
    \/ TruncateLedgerAction

SpecMultiNode == Init /\ [][NextMultiNodeAction]_vars

-----------------------------------------------------------------------------
\* Bounded model-checking variants

\* Limit the number of view changes
MCTruncateLedgerAction ==
    /\ Len(ledgerBranches) < ViewLimit
    /\ TruncateLedgerAction

\* Limit the length of the history
MCRwTxnRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ RwTxnRequestAction

MCRwTxnResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ RwTxnResponseAction

MCStatusCommittedResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ StatusCommittedResponseAction

MCStatusInvalidResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ StatusInvalidResponseAction

MCNextMultiNodeAction ==
    \/ MCRwTxnRequestAction
    \/ RwTxnExecuteAction
    \/ MCRwTxnResponseAction
    \/ MCStatusCommittedResponseAction
    \/ MCStatusInvalidResponseAction
    \/ MCTruncateLedgerAction

MCSpecMultiNode == Init /\ [][MCNextMultiNodeAction]_vars

Next == MCNextMultiNodeAction

Spec == MCSpecMultiNode

-----------------------------------------------------------------------------
\* Safety invariants

TypeOK ==
    /\ history \in Seq([type : {RwTxnRequest}, tx : Nat]
                       \cup [type : {RwTxnResponse}, tx : Nat, tx_id : Nat \X Nat]
                       \cup [type : {TxStatusReceived}, tx_id : Nat \X Nat,
                             status : {CommittedStatus, InvalidStatus}])
    /\ ledgerBranches \in Seq(Seq([view : Nat, tx : Nat]))
    /\ Len(ledgerBranches) >= 1

\* Bound respected
ViewLimitInv == Len(ledgerBranches) <= ViewLimit

\* No transaction is reported both committed and invalid
CommittedNotInvalidInv ==
    \A j \in DOMAIN history :
        (history[j].type = TxStatusReceived
            /\ history[j].status = CommittedStatus)
        => ~HasStatus(history[j].tx_id, InvalidStatus)

\* Committed transactions remain in the current ledger forever
CommittedPersistInv ==
    \A j \in DOMAIN history :
        (history[j].type = TxStatusReceived
            /\ history[j].status = CommittedStatus)
        => LET v == history[j].tx_id[1]
               s == history[j].tx_id[2]
           IN /\ s \in DOMAIN Ledger
              /\ Ledger[s].view = v

\* A transaction appears at most once in any ledger branch
UniqueTxInLedgerInv ==
    \A b \in DOMAIN ledgerBranches :
        \A k1, k2 \in DOMAIN ledgerBranches[b] :
            ledgerBranches[b][k1].tx = ledgerBranches[b][k2].tx => k1 = k2

=============================================================================