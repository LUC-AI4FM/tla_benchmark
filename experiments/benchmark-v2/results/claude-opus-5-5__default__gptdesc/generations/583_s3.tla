---------------------------- MODULE MultiNode ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Txs,            \* identifiers of read-write transactions issued by clients
    ViewLimit,      \* bound on the number of views (ledger branches)
    HistoryLimit    \* bound on the length of the external history

ASSUME /\ Txs # {}
       /\ ViewLimit \in Nat \ {0}
       /\ HistoryLimit \in Nat

\* Event types in the external (client-observable) history
RwTxRequest      == "RwTxRequest"
RwTxResponse     == "RwTxResponse"
TxStatusReceived == "TxStatusReceived"

\* Transaction status values
CommittedStatus == "CommittedStatus"
InvalidStatus   == "InvalidStatus"

VARIABLES
    history,        \* sequence of client-observable events
    ledgerBranches, \* ledgerBranches[v] is the ledger as of view v
    commitSeqNum    \* highest committed sequence number

vars == <<history, ledgerBranches, commitSeqNum>>

-----------------------------------------------------------------------------
\* Helpers

CurrentView == Len(ledgerBranches)
Latest      == ledgerBranches[CurrentView]

Views   == 1..ViewLimit
SeqNums == 1..(Cardinality(Txs) * ViewLimit)
TxIDs   == Views \X SeqNums

LedgerEntries == [view : Views, tx : Txs]

HistoryEvents ==
         [type : {RwTxRequest}, tx : Txs]
    \cup [type : {RwTxResponse}, tx : Txs, tx_id : TxIDs]
    \cup [type : {TxStatusReceived}, tx_id : TxIDs,
          status : {CommittedStatus, InvalidStatus}]

Requested(t) == \E i \in DOMAIN history :
                    history[i].type = RwTxRequest /\ history[i].tx = t

Responded(t) == \E i \in DOMAIN history :
                    history[i].type = RwTxResponse /\ history[i].tx = t

InLatest(t)  == \E s \in DOMAIN Latest : Latest[s].tx = t

StatusSent(tid, st) ==
    \E i \in DOMAIN history :
        /\ history[i].type = TxStatusReceived
        /\ history[i].tx_id = tid
        /\ history[i].status = st

-----------------------------------------------------------------------------
\* Initial state

Init ==
    /\ history = <<>>
    /\ ledgerBranches = << <<>> >>
    /\ commitSeqNum = 0

-----------------------------------------------------------------------------
\* Single-node behaviour

\* A client submits a new read-write transaction
RwTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ \E t \in Txs :
        /\ ~Requested(t)
        /\ history' = Append(history, [type |-> RwTxRequest, tx |-> t])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

\* The node executes a requested transaction, appending it to the current branch
RwTxExecuteAction ==
    /\ \E t \in Txs :
        /\ Requested(t)
        /\ ~Responded(t)
        /\ ~InLatest(t)
        /\ ledgerBranches' =
             [ledgerBranches EXCEPT ![CurrentView] =
                 Append(@, [view |-> CurrentView, tx |-> t])]
    /\ UNCHANGED <<history, commitSeqNum>>

\* The node replies to the client with the transaction id
RwTxResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E s \in DOMAIN Latest :
        /\ ~Responded(Latest[s].tx)
        /\ history' = Append(history,
              [type  |-> RwTxResponse,
               tx    |-> Latest[s].tx,
               tx_id |-> <<Latest[s].view, s>>])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

\* The commit point advances along the current branch
CommitAction ==
    /\ commitSeqNum < Len(Latest)
    /\ \E i \in (commitSeqNum + 1)..Len(Latest) :
        commitSeqNum' = i
    /\ UNCHANGED <<history, ledgerBranches>>

\* The node reports that a transaction has been committed
StatusCommittedResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        /\ LET v == history[i].tx_id[1]
               s == history[i].tx_id[2]
           IN /\ s <= commitSeqNum
              /\ Latest[s].view = v
              /\ ~StatusSent(<<v, s>>, CommittedStatus)
              /\ history' = Append(history,
                    [type   |-> TxStatusReceived,
                     tx_id  |-> <<v, s>>,
                     status |-> CommittedStatus])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

NextSingleNodeAction ==
    \/ RwTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ CommitAction
    \/ StatusCommittedResponseAction

-----------------------------------------------------------------------------
\* Multi-node behaviour

\* Simulates a leader election: truncate an uncommitted suffix of the current
\* branch and start a new branch (new view) from the remaining prefix.
TruncateLedgerAction ==
    /\ CurrentView < ViewLimit
    /\ \E i \in commitSeqNum..Len(Latest) :
        ledgerBranches' = Append(ledgerBranches, SubSeq(Latest, 1, i))
    /\ UNCHANGED <<history, commitSeqNum>>

\* The node reports a transaction as invalid once it can no longer be committed
\* in the current or any future view: its view is older than the current one
\* and the current branch does not hold it at its sequence number.
StatusInvalidResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        /\ LET v == history[i].tx_id[1]
               s == history[i].tx_id[2]
           IN /\ v < CurrentView
              /\ \/ Len(Latest) < s
                 \/ Latest[s].view # v
              /\ ~StatusSent(<<v, s>>, InvalidStatus)
              /\ history' = Append(history,
                    [type   |-> TxStatusReceived,
                     tx_id  |-> <<v, s>>,
                     status |-> InvalidStatus])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

NextMultiNodeAction ==
    \/ NextSingleNodeAction
    \/ TruncateLedgerAction
    \/ StatusInvalidResponseAction

Spec == Init /\ [][NextMultiNodeAction]_vars

-----------------------------------------------------------------------------
\* Invariants

TypeOK ==
    /\ history \in Seq(HistoryEvents)
    /\ Len(ledgerBranches) \in Views
    /\ \A v \in DOMAIN ledgerBranches : ledgerBranches[v] \in Seq(LedgerEntries)
    /\ commitSeqNum \in Nat
    /\ commitSeqNum <= Len(Latest)

\* A transaction is never reported both committed and invalid
CommittedOrInvalidExclusive ==
    \A i, j \in DOMAIN history :
        ( /\ history[i].type = TxStatusReceived
          /\ history[j].type = TxStatusReceived
          /\ history[i].tx_id = history[j].tx_id )
        => history[i].status = history[j].status

\* Transactions reported committed remain in the current ledger
CommittedTxsPersist ==
    \A i \in DOMAIN history :
        ( /\ history[i].type = TxStatusReceived
          /\ history[i].status = CommittedStatus )
        => /\ history[i].tx_id[2] <= Len(Latest)
           /\ Latest[history[i].tx_id[2]].view = history[i].tx_id[1]

\* The committed prefix is shared by every branch created after it was committed
CommittedPrefixStable ==
    \A s \in 1..commitSeqNum :
        Latest[s] = ledgerBranches[CurrentView][s]

=============================================================================