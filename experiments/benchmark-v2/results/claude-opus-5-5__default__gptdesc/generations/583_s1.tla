---------------------------- MODULE MultiNode ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Txs,
    MaxViews

ASSUME MaxViews \in Nat \ {0}

VARIABLES
    history,
    ledgerBranches,
    commitIndex

vars == <<history, ledgerBranches, commitIndex>>

-----------------------------------------------------------------------------
(* Message types and statuses *)

RwTxRequest      == "RwTxRequest"
RwTxResponse     == "RwTxResponse"
TxStatusReceived == "TxStatusReceived"

CommittedStatus  == "CommittedStatus"
InvalidStatus    == "InvalidStatus"
TxStatuses       == {CommittedStatus, InvalidStatus}

Views         == 1..MaxViews
TxIDs         == Views \X (Nat \ {0})
LedgerEntries == [view : Views, tx : Txs]

Messages ==
         [type : {RwTxRequest}, tx : Txs]
    \cup [type : {RwTxResponse}, tx : Txs, tx_id : TxIDs]
    \cup [type : {TxStatusReceived}, tx_id : TxIDs, status : TxStatuses]

CurrentView   == Len(ledgerBranches)
CurrentLedger == ledgerBranches[CurrentView]

StatusSent(txid, st) ==
    \E j \in DOMAIN history :
        /\ history[j].type = TxStatusReceived
        /\ history[j].tx_id = txid
        /\ history[j].status = st

-----------------------------------------------------------------------------
(* Single-node behaviour *)

Init ==
    /\ history = <<>>
    /\ ledgerBranches = << <<>> >>
    /\ commitIndex = 0

\* A client submits a new read-write transaction
RwTxRequestAction ==
    /\ \E tx \in Txs :
        /\ \A i \in DOMAIN history :
              ~(history[i].type = RwTxRequest /\ history[i].tx = tx)
        /\ history' = Append(history, [type |-> RwTxRequest, tx |-> tx])
    /\ UNCHANGED <<ledgerBranches, commitIndex>>

\* The leader executes a requested transaction, appending it to the ledger
RwTxExecuteAction ==
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxRequest
        /\ \A s \in DOMAIN CurrentLedger : CurrentLedger[s].tx # history[i].tx
        /\ ledgerBranches' =
              [ledgerBranches EXCEPT ![CurrentView] =
                  Append(@, [view |-> CurrentView, tx |-> history[i].tx])]
    /\ UNCHANGED <<history, commitIndex>>

\* The leader replies to the client with the transaction ID
RwTxResponseAction ==
    /\ \E s \in DOMAIN CurrentLedger :
        LET txid == <<CurrentLedger[s].view, s>>
        IN
        /\ \A i \in DOMAIN history :
              ~(history[i].type = RwTxResponse /\ history[i].tx_id = txid)
        /\ history' = Append(history,
                         [type  |-> RwTxResponse,
                          tx    |-> CurrentLedger[s].tx,
                          tx_id |-> txid])
    /\ UNCHANGED <<ledgerBranches, commitIndex>>

\* The commit index advances along the current branch
CommitAction ==
    /\ commitIndex < Len(CurrentLedger)
    /\ \E s \in (commitIndex + 1)..Len(CurrentLedger) : commitIndex' = s
    /\ UNCHANGED <<history, ledgerBranches>>

\* Report a committed status for a transaction that has been committed
StatusCommittedResponseAction ==
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        /\ LET v == history[i].tx_id[1]
               s == history[i].tx_id[2]
           IN
           /\ s <= commitIndex
           /\ CurrentLedger[s].view = v
           /\ ~StatusSent(history[i].tx_id, CommittedStatus)
           /\ history' = Append(history,
                            [type   |-> TxStatusReceived,
                             tx_id  |-> history[i].tx_id,
                             status |-> CommittedStatus])
    /\ UNCHANGED <<ledgerBranches, commitIndex>>

NextSingleNodeAction ==
    \/ RwTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ CommitAction
    \/ StatusCommittedResponseAction

-----------------------------------------------------------------------------
(* Multi-node extensions *)

\* Simulates leader election: truncates some uncommitted suffix of the current
\* branch and starts a new branch (i.e. a new view)
TruncateLedgerAction ==
    /\ CurrentView < MaxViews
    /\ \E i \in commitIndex..Len(CurrentLedger) :
          ledgerBranches' = Append(ledgerBranches, SubSeq(CurrentLedger, 1, i))
    /\ UNCHANGED <<history, commitIndex>>

\* Report an invalid status for a transaction that can no longer be committed
\* in the current or any future view
StatusInvalidResponseAction ==
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        /\ LET v == history[i].tx_id[1]
               s == history[i].tx_id[2]
           IN
           /\ CurrentView > v
           /\ \/ s > Len(CurrentLedger)
              \/ CurrentLedger[s].view # v
           /\ ~StatusSent(history[i].tx_id, InvalidStatus)
           /\ history' = Append(history,
                            [type   |-> TxStatusReceived,
                             tx_id  |-> history[i].tx_id,
                             status |-> InvalidStatus])
    /\ UNCHANGED <<ledgerBranches, commitIndex>>

NextMultiNodeAction ==
    \/ NextSingleNodeAction
    \/ TruncateLedgerAction
    \/ StatusInvalidResponseAction

Spec == Init /\ [][NextMultiNodeAction]_vars

-----------------------------------------------------------------------------
(* Properties *)

TypeOK ==
    /\ history \in Seq(Messages)
    /\ ledgerBranches \in Seq(Seq(LedgerEntries))
    /\ Len(ledgerBranches) \in Views
    /\ commitIndex \in Nat

CommitIndexInBounds ==
    commitIndex <= Len(CurrentLedger)

\* A transaction is never reported both committed and invalid
CommittedNotInvalidInv ==
    \A i, j \in DOMAIN history :
        ~( /\ history[i].type = TxStatusReceived
           /\ history[j].type = TxStatusReceived
           /\ history[i].tx_id = history[j].tx_id
           /\ history[i].status = CommittedStatus
           /\ history[j].status = InvalidStatus )

\* Committed prefix is never rolled back
CommittedPrefixStable ==
    [][ /\ commitIndex' >= commitIndex
        /\ \A s \in 1..commitIndex : CurrentLedger'[s] = CurrentLedger[s]
      ]_vars

=============================================================================