---------------------------- MODULE MultiNodeLedgerReads ----------------------------
(***************************************************************************)
(* A distributed ledger with read-write transactions, view-based          *)
(* transaction IDs <<view, seqnum>>, ledger branches (forks) caused by    *)
(* view changes, and transaction status notifications.                    *)
(*                                                                         *)
(* ledgerBranches[v] is the ledger as seen in view v. A view change makes  *)
(* a new branch by copying a prefix of the latest branch that includes at  *)
(* least the committed prefix. Transactions are then appended to the       *)
(* latest branch. commitIndex is the length of the committed prefix of     *)
(* the latest branch. A committed prefix is never rolled back.             *)
(*                                                                         *)
(* history records the client-observable events: requests, responses and   *)
(* status notifications.                                                   *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    NumRwTxs,   \* number of read-write transactions clients may submit
    MaxView     \* maximum number of views, which is the number of branches

ASSUME NumRwTxs \in Nat \ {0}
ASSUME MaxView \in Nat \ {0}

VARIABLES
    history,        \* sequence of client-observable events
    ledgerBranches, \* sequence of branches, indexed by view
    commitIndex     \* length of the committed prefix of the latest branch

vars == <<history, ledgerBranches, commitIndex>>

-----------------------------------------------------------------------------
(* Event and status tags *)
RwTxRequest      == "RwTxRequest"
RwTxResponse     == "RwTxResponse"
TxStatusReceived == "TxStatusReceived"
CommittedStatus  == "CommittedStatus"
InvalidStatus    == "InvalidStatus"

Txs   == 1..NumRwTxs
Views == 1..MaxView

Min(a, b) == IF a <= b THEN a ELSE b

-----------------------------------------------------------------------------
(* Helper operators *)

CurrentView == Len(ledgerBranches)
Last        == ledgerBranches[CurrentView]

TxsInBranch(b) == { b[k].tx : k \in DOMAIN b }

RequestIdx  == { i \in DOMAIN history : history[i].type = RwTxRequest }
ResponseIdx == { i \in DOMAIN history : history[i].type = RwTxResponse }
StatusIdx   == { i \in DOMAIN history : history[i].type = TxStatusReceived }

RequestedTxs == { history[i].tx : i \in RequestIdx }
RespondedTxs == { history[i].tx : i \in ResponseIdx }
Responses    == { history[i] : i \in ResponseIdx }

HasStatus(txid) == \E i \in StatusIdx : history[i].tx_id = txid

IsCommitted(txid) ==
    \E i \in StatusIdx : history[i].tx_id = txid /\ history[i].status = CommittedStatus

IsInvalid(txid) ==
    \E i \in StatusIdx : history[i].tx_id = txid /\ history[i].status = InvalidStatus

CommittedResponses == { r \in Responses : IsCommitted(r.tx_id) }

IsPrefix(s, t) == Len(s) <= Len(t) /\ SubSeq(t, 1, Len(s)) = s

-----------------------------------------------------------------------------
(* Type invariant *)

EntryOK(e) == e.view \in Views /\ e.tx \in Txs

EventOK(e) ==
    \/ /\ e.type = RwTxRequest
       /\ e.tx \in Txs
    \/ /\ e.type = RwTxResponse
       /\ e.tx \in Txs
       /\ e.tx_id[1] \in Views
       /\ e.tx_id[2] \in 1..NumRwTxs
       /\ \A k \in DOMAIN e.observed : e.observed[k] \in Txs
    \/ /\ e.type = TxStatusReceived
       /\ e.tx_id[1] \in Views
       /\ e.tx_id[2] \in 1..NumRwTxs
       /\ e.status \in {CommittedStatus, InvalidStatus}

TypeOK ==
    /\ \A i \in DOMAIN history : EventOK(history[i])
    /\ Len(ledgerBranches) \in Views
    /\ \A v \in DOMAIN ledgerBranches :
           \A k \in DOMAIN ledgerBranches[v] : EntryOK(ledgerBranches[v][k])
    /\ commitIndex \in 0..Len(Last)

-----------------------------------------------------------------------------
(* Initial states *)

Init ==
    /\ history = <<>>
    /\ ledgerBranches = << <<>> >>
    /\ commitIndex = 0

(* Alternative initial state that starts in the middle of an execution.
   Two branches exist. Transactions 1, 2 and 3 have been requested and
   responded to. Transactions <<1,1>> and <<2,2>> are committed.
   Requires NumRwTxs >= 3 and MaxView >= 2. *)
InitAlt ==
    /\ ledgerBranches =
         << << [view |-> 1, tx |-> 1] >>,
            << [view |-> 1, tx |-> 1],
               [view |-> 2, tx |-> 2],
               [view |-> 2, tx |-> 3] >> >>
    /\ commitIndex = 2
    /\ history =
         << [type |-> RwTxRequest, tx |-> 1],
            [type |-> RwTxResponse, tx |-> 1, tx_id |-> <<1, 1>>, observed |-> <<>>],
            [type |-> RwTxRequest, tx |-> 2],
            [type |-> RwTxResponse, tx |-> 2, tx_id |-> <<2, 2>>, observed |-> <<1>>],
            [type |-> TxStatusReceived, tx_id |-> <<1, 1>>, status |-> CommittedStatus],
            [type |-> RwTxRequest, tx |-> 3],
            [type |-> TxStatusReceived, tx_id |-> <<2, 2>>, status |-> CommittedStatus],
            [type |-> RwTxResponse, tx |-> 3, tx_id |-> <<2, 3>>, observed |-> <<1, 2>>] >>

-----------------------------------------------------------------------------
(* Actions *)

(* A client submits a new read-write transaction. *)
RwTxRequestAction ==
    /\ Cardinality(RequestIdx) < NumRwTxs
    /\ history' = Append(history,
                    [type |-> RwTxRequest, tx |-> Cardinality(RequestIdx) + 1])
    /\ UNCHANGED <<ledgerBranches, commitIndex>>

(* The primary of the current view executes a requested transaction and
   appends it to the latest branch. *)
RwTxExecuteAction ==
    \E t \in RequestedTxs :
        /\ t \notin RespondedTxs
        /\ t \notin TxsInBranch(Last)
        /\ ledgerBranches' = [ledgerBranches EXCEPT ![CurrentView] =
                                 Append(@, [view |-> CurrentView, tx |-> t])]
        /\ UNCHANGED <<history, commitIndex>>

(* The primary responds to a transaction executed in the current view. The
   response carries the transaction ID and the transactions it observed. *)
RwTxResponseAction ==
    \E s \in DOMAIN Last :
        /\ Last[s].view = CurrentView
        /\ Last[s].tx \notin RespondedTxs
        /\ history' = Append(history,
              [type     |-> RwTxResponse,
               tx       |-> Last[s].tx,
               tx_id    |-> <<Last[s].view, s>>,
               observed |-> [k \in 1..(s - 1) |-> Last[k].tx]])
        /\ UNCHANGED <<ledgerBranches, commitIndex>>

(* The committed prefix of the latest branch grows. *)
IncreaseCommitIndexAction ==
    /\ commitIndex < Len(Last)
    /\ \E c \in (commitIndex + 1)..Len(Last) : commitIndex' = c
    /\ UNCHANGED <<history, ledgerBranches>>

(* A view change creates a new branch. The new branch keeps a prefix of the
   latest branch that contains at least the committed prefix. *)
AppendOtherBranchAction ==
    /\ Len(ledgerBranches) < MaxView
    /\ \E k \in commitIndex..Len(Last) :
          ledgerBranches' = Append(ledgerBranches, SubSeq(Last, 1, k))
    /\ UNCHANGED <<history, commitIndex>>

(* The client learns that a transaction ID is committed. *)
StatusCommittedResponseAction ==
    \E r \in Responses :
        LET v == r.tx_id[1]
            s == r.tx_id[2]
        IN /\ ~HasStatus(r.tx_id)
           /\ s <= commitIndex
           /\ Last[s].view = v
           /\ history' = Append(history,
                 [type |-> TxStatusReceived, tx_id |-> r.tx_id, status |-> CommittedStatus])
           /\ UNCHANGED <<ledgerBranches, commitIndex>>

(* The client learns that a transaction ID is invalid. A committed entry
   from a later view at or before seqnum s means <<v, s>> can never commit. *)
StatusInvalidResponseAction ==
    \E r \in Responses :
        LET v == r.tx_id[1]
            s == r.tx_id[2]
        IN /\ ~HasStatus(r.tx_id)
           /\ \E k \in 1..Min(s, commitIndex) : Last[k].view > v
           /\ history' = Append(history,
                 [type |-> TxStatusReceived, tx_id |-> r.tx_id, status |-> InvalidStatus])
           /\ UNCHANGED <<ledgerBranches, commitIndex>>

Next ==
    \/ RwTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ IncreaseCommitIndexAction
    \/ AppendOtherBranchAction
    \/ StatusCommittedResponseAction
    \/ StatusInvalidResponseAction

Fairness ==
    /\ WF_vars(RwTxRequestAction)
    /\ WF_vars(IncreaseCommitIndexAction)

Spec    == Init    /\ [][Next]_vars /\ Fairness
SpecAlt == InitAlt /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety invariants *)

(* Every response is preceded by a request for the same transaction. *)
AllRwReceivedIsFirstSentInv ==
    \A i \in ResponseIdx :
        \E j \in RequestIdx : j < i /\ history[j].tx = history[i].tx

(* Every status notification follows a response with that transaction ID. *)
StatusFollowsResponseInv ==
    \A i \in StatusIdx :
        \E j \in ResponseIdx : j < i /\ history[j].tx_id = history[i].tx_id

(* Every transaction gets at most one response. Distinct responses have
   distinct transaction IDs. *)
UniqueResponsesInv ==
    \A i, j \in ResponseIdx :
        i /= j => /\ history[i].tx /= history[j].tx
                  /\ history[i].tx_id /= history[j].tx_id

(* A transaction ID is never both committed and invalid. *)
CommittedOrInvalidExclusiveInv ==
    \A r \in Responses : ~(IsCommitted(r.tx_id) /\ IsInvalid(r.tx_id))

(* Read consistency. A response observes only previously requested
   transactions, never itself, with no duplicates, and the number of
   observed transactions matches its seqnum. *)
ReadConsistencyInv ==
    \A r \in Responses :
        /\ Len(r.observed) = r.tx_id[2] - 1
        /\ \A k \in DOMAIN r.observed :
              /\ r.observed[k] \in RequestedTxs
              /\ r.observed[k] /= r.tx
        /\ \A k1, k2 \in DOMAIN r.observed :
              k1 /= k2 => r.observed[k1] /= r.observed[k2]

(* Serializability of committed transactions. Committed transactions form a
   single total order by seqnum. Each committed transaction observed
   exactly the committed transactions before it in that order. *)
CommittedRwSerializableInv ==
    \A a, b \in CommittedResponses :
        a.tx_id[2] < b.tx_id[2] =>
            /\ IsPrefix(a.observed, b.observed)
            /\ b.observed[a.tx_id[2]] = a.tx

(* Two committed transactions never share a seqnum. *)
CommittedSeqnumsUniqueInv ==
    \A a, b \in CommittedResponses :
        a.tx_id[2] = b.tx_id[2] => a = b

(* Branch consistency. A committed transaction ID is in the committed
   prefix of the latest branch. *)
CommittedInLedgerInv ==
    \A a \in CommittedResponses :
        /\ a.tx_id[2] <= commitIndex
        /\ Last[a.tx_id[2]] = [view |-> a.tx_id[1], tx |-> a.tx]

(* Branch consistency. Views never decrease along any branch. Each branch
   v contains only entries from views <= v. Each branch extends a prefix
   of its predecessor. *)
BranchConsistencyInv ==
    /\ \A v \in DOMAIN ledgerBranches :
          /\ \A k \in DOMAIN ledgerBranches[v] : ledgerBranches[v][k].view <= v
          /\ \A k1, k2 \in DOMAIN ledgerBranches[v] :
                k1 < k2 => ledgerBranches[v][k1].view <= ledgerBranches[v][k2].view
    /\ \A v \in DOMAIN ledgerBranches :
          v > 1 =>
             LET pre == SelectSeq(ledgerBranches[v], LAMBDA e : e.view < v)
             IN IsPrefix(pre, ledgerBranches[v - 1])

(* Each transaction appears at most once in a branch. *)
NoDuplicateInBranchInv ==
    \A v \in DOMAIN ledgerBranches :
        \A k1, k2 \in DOMAIN ledgerBranches[v] :
            k1 /= k2 => ledgerBranches[v][k1].tx /= ledgerBranches[v][k2].tx

-----------------------------------------------------------------------------
(* Temporal properties *)

(* The committed prefix is never rolled back. *)
CommittedPrefixStableProp ==
    [][ /\ commitIndex' >= commitIndex
        /\ IsPrefix(SubSeq(Last, 1, commitIndex),
                    ledgerBranches'[Len(ledgerBranches')]) ]_vars

(* History is append-only. *)
HistoryMonotonicProp ==
    [][ IsPrefix(history, history') ]_vars

(* Liveness. All transactions are eventually requested. *)
AllRequestsEventuallyMadeProp ==
    <>(Cardinality(RequestIdx) = NumRwTxs)

(* Liveness. The commit index eventually catches up with the latest branch. *)
EventuallyAllCommittedProp ==
    <>(commitIndex = Len(Last))

=============================================================================