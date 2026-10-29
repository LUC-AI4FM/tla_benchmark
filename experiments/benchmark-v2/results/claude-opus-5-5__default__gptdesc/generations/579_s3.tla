---------------------------- MODULE MCMultiNode ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* Base MultiNode model (inlined here so the module parses on its own)

CONSTANTS
    HistoryLimit,   \* Bound on the length of the client-observed history
    ViewLimit       \* Bound on the number of view changes (ledger branches)

ASSUME HistoryLimit \in Nat
ASSUME ViewLimit \in Nat \ {0}

VARIABLES
    history,        \* Sequence of client-observed events
    ledgerBranches, \* Sequence of ledger branches, one per view
    commitIndex     \* Commit index of the latest ledger branch

vars == <<history, ledgerBranches, commitIndex>>

\* Event types
RwTxRequest      == "RwTxRequest"
RwTxResponse     == "RwTxResponse"
TxStatusReceived == "TxStatusReceived"

\* Transaction statuses
CommittedStatus == "CommittedStatus"
InvalidStatus   == "InvalidStatus"

Last(s) == s[Len(s)]

LedgerEntries == [view : Nat, tx : Nat]

NextRequestId ==
    Cardinality({i \in DOMAIN history : history[i].type = RwTxRequest}) + 1

TypeOK ==
    /\ history \in Seq(
          [type : {RwTxRequest}, tx : Nat]
          \cup [type : {RwTxResponse}, tx : Nat, tx_id : Nat \X Nat]
          \cup [type : {TxStatusReceived}, tx_id : Nat \X Nat,
                status : {CommittedStatus, InvalidStatus}])
    /\ ledgerBranches \in Seq(Seq(LedgerEntries))
    /\ Len(ledgerBranches) >= 1
    /\ commitIndex \in 0..Len(Last(ledgerBranches))

Init ==
    /\ history = <<>>
    /\ ledgerBranches = << <<>> >>
    /\ commitIndex = 0

\* A client submits a new read-write transaction
RwTxRequestAction ==
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> NextRequestId])
    /\ UNCHANGED <<ledgerBranches, commitIndex>>

\* The current primary executes a requested transaction in the current view
RwTxExecuteAction ==
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxRequest
        /\ \A k \in DOMAIN Last(ledgerBranches) :
              Last(ledgerBranches)[k].tx # history[i].tx
        /\ ledgerBranches' =
              [ledgerBranches EXCEPT ![Len(ledgerBranches)] =
                  Append(@, [view |-> Len(ledgerBranches), tx |-> history[i].tx])]
    /\ UNCHANGED <<history, commitIndex>>

\* The client receives a response with a transaction ID for an executed transaction
RwTxResponseAction ==
    /\ \E view \in DOMAIN ledgerBranches :
        \E seqno \in DOMAIN ledgerBranches[view] :
            /\ ledgerBranches[view][seqno].view = view
            /\ LET tx == ledgerBranches[view][seqno].tx IN
                /\ ~\E j \in DOMAIN history :
                        /\ history[j].type = RwTxResponse
                        /\ history[j].tx = tx
                /\ history' = Append(history,
                        [type |-> RwTxResponse, tx |-> tx, tx_id |-> <<view, seqno>>])
    /\ UNCHANGED <<ledgerBranches, commitIndex>>

\* The commit index of the latest branch advances
IncreaseCommitAction ==
    /\ \E i \in (commitIndex + 1)..Len(Last(ledgerBranches)) :
        commitIndex' = i
    /\ UNCHANGED <<history, ledgerBranches>>

\* View change: a new branch is started from a prefix of the latest branch
\* that includes at least all committed entries
TruncateLedgerAction ==
    /\ \E i \in commitIndex..Len(Last(ledgerBranches)) :
        ledgerBranches' = Append(ledgerBranches, SubSeq(Last(ledgerBranches), 1, i))
    /\ UNCHANGED <<history, commitIndex>>

\* The client learns a transaction is committed
StatusCommittedResponseAction ==
    /\ \E j \in DOMAIN history :
        /\ history[j].type = RwTxResponse
        /\ LET id == history[j].tx_id IN
            /\ id[2] <= commitIndex
            /\ Last(ledgerBranches)[id[2]].view = id[1]
            /\ history' = Append(history,
                    [type |-> TxStatusReceived, tx_id |-> id, status |-> CommittedStatus])
    /\ UNCHANGED <<ledgerBranches, commitIndex>>

\* The client learns a transaction is invalid
StatusInvalidResponseAction ==
    /\ \E j \in DOMAIN history :
        /\ history[j].type = RwTxResponse
        /\ LET id == history[j].tx_id IN
            /\ id[2] <= commitIndex
            /\ Last(ledgerBranches)[id[2]].view # id[1]
            /\ history' = Append(history,
                    [type |-> TxStatusReceived, tx_id |-> id, status |-> InvalidStatus])
    /\ UNCHANGED <<ledgerBranches, commitIndex>>

Next ==
    \/ RwTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ IncreaseCommitAction
    \/ TruncateLedgerAction
    \/ StatusCommittedResponseAction
    \/ StatusInvalidResponseAction

Spec == Init /\ [][Next]_vars

\* Safety invariants

\* Committed transactions are in the latest ledger branch at their recorded position and view
CommittedTxInLedgerInv ==
    \A j \in DOMAIN history :
        (history[j].type = TxStatusReceived /\ history[j].status = CommittedStatus)
            => /\ history[j].tx_id[2] <= Len(Last(ledgerBranches))
               /\ Last(ledgerBranches)[history[j].tx_id[2]].view = history[j].tx_id[1]

\* No transaction ID is reported as both committed and invalid
CommittedOrInvalidInv ==
    \A i, j \in DOMAIN history :
        (/\ history[i].type = TxStatusReceived
         /\ history[j].type = TxStatusReceived
         /\ history[i].tx_id = history[j].tx_id)
            => history[i].status = history[j].status

\* Bounded model-checking wrapper

MCRwTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ RwTxRequestAction

MCRwTxExecuteAction ==
    /\ Len(ledgerBranches) <= ViewLimit
    /\ RwTxExecuteAction

MCRwTxResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ RwTxResponseAction

MCIncreaseCommitAction ==
    IncreaseCommitAction

\* Bound the number of view changes
MCTruncateLedgerAction ==
    /\ Len(ledgerBranches) < ViewLimit
    /\ TruncateLedgerAction

MCStatusCommittedResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ StatusCommittedResponseAction

MCStatusInvalidResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ StatusInvalidResponseAction

MCNextMultiNodeAction ==
    \/ MCRwTxRequestAction
    \/ MCRwTxExecuteAction
    \/ MCRwTxResponseAction
    \/ MCIncreaseCommitAction
    \/ MCTruncateLedgerAction
    \/ MCStatusCommittedResponseAction
    \/ MCStatusInvalidResponseAction

MCSpecMultiNode == Init /\ [][MCNextMultiNodeAction]_vars

THEOREM MCSpecMultiNode => [](TypeOK /\ CommittedTxInLedgerInv /\ CommittedOrInvalidInv)

=============================================================================