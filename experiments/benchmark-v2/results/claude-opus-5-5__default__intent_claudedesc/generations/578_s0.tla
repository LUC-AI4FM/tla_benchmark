--------------------------- MODULE MultiNodeReads ---------------------------
(***************************************************************************)
(* Multi-node distributed read operations.                                 *)
(*                                                                         *)
(* This module has no dependencies on other modules. It contains three     *)
(* parts.                                                                  *)
(*  (1) Multi-node infrastructure. A leader per view executes read-write   *)
(*      transactions on its ledger branch. Elections start a new view and  *)
(*      may truncate uncommitted suffixes. The commit index advances.      *)
(*      Clients learn the status of transaction IDs.                       *)
(*  (2) Single-node read semantics. A read observes a prefix of one        *)
(*      node's ledger branch. Its transaction ID is <<view, seqno>>.       *)
(*  (3) Distributed read-only transactions. Clients may issue RO requests  *)
(*      at any time. Any node in any view may serve an RO request, so the  *)
(*      read can be stale. Each RO request gets exactly one response.      *)
(*                                                                         *)
(* Consistency guarantee: a read whose transaction ID is later reported as *)
(* Committed has observed exactly a prefix of the committed ledger.        *)
(* That makes it serializable with respect to the committed history.       *)
(* A read that is reported Invalid was never committed.                    *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    MaxRequests,     \* bound on the number of client requests (RW + RO)
    MaxViews         \* bound on the number of views (elections)

ASSUME MaxRequests \in Nat \ {0}
ASSUME MaxViews \in Nat \ {0}

\* Event types
RwTxRequest      == "RwTxRequest"
RwTxResponse     == "RwTxResponse"
RoTxRequest      == "RoTxRequest"
RoTxResponse     == "RoTxResponse"
TxStatusReceived == "TxStatusReceived"

\* Status values
CommittedStatus == "Committed"
InvalidStatus   == "Invalid"

VARIABLES
    history,         \* sequence of client-observable events
    ledgerBranches,  \* ledgerBranches[v] = ledger of the leader of view v
    commitSeqNum     \* commit index of the current leader's ledger

vars == <<history, ledgerBranches, commitSeqNum>>

TxIds == 1..MaxRequests
Views == 1..MaxViews

-----------------------------------------------------------------------------
(* Helpers *)

CurrentView  == Len(ledgerBranches)
LeaderBranch == ledgerBranches[CurrentView]

CommittedLedger == SubSeq(LeaderBranch, 1, commitSeqNum)

\* Transaction ids observed by reading the first i entries of a branch
ObservedPrefix(branch, i) == [k \in 1..i |-> branch[k].tx]

TxInBranch(tx, branch) == \E k \in 1..Len(branch) : branch[k].tx = tx

RequestIndices ==
    {i \in DOMAIN history : history[i].type \in {RwTxRequest, RoTxRequest}}

NumRequests == Cardinality(RequestIndices)

IsRwRequest(tx) ==
    \E i \in DOMAIN history : history[i].type = RwTxRequest /\ history[i].tx = tx

IsRoRequest(tx) ==
    \E i \in DOMAIN history : history[i].type = RoTxRequest /\ history[i].tx = tx

HasResponse(tx) ==
    \E i \in DOMAIN history :
        /\ history[i].type \in {RwTxResponse, RoTxResponse}
        /\ history[i].tx = tx

ResponseTxIds ==
    { history[i].tx_id : i \in
        {j \in DOMAIN history : history[j].type \in {RwTxResponse, RoTxResponse}} }

HasStatus(txid, st) ==
    \E i \in DOMAIN history :
        /\ history[i].type = TxStatusReceived
        /\ history[i].tx_id = txid
        /\ history[i].status = st

\* Status as determined by the current leader
IsCommittedTxId(txid) ==
    /\ txid[2] \in 1..commitSeqNum
    /\ LeaderBranch[txid[2]].view = txid[1]

IsInvalidTxId(txid) ==
    \/ /\ txid[2] \in 1..commitSeqNum
       /\ LeaderBranch[txid[2]].view # txid[1]
    \/ /\ txid[1] < CurrentView
       /\ \/ txid[2] > Len(LeaderBranch)
          \/ LeaderBranch[txid[2]].view # txid[1]

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ history = <<>>
    /\ ledgerBranches = << <<>> >>
    /\ commitSeqNum = 0

-----------------------------------------------------------------------------
(* Multi-node actions *)

\* Client submits a read-write transaction
RwTxRequestAction ==
    /\ NumRequests < MaxRequests
    /\ history' = Append(history,
                    [type |-> RwTxRequest, tx |-> NumRequests + 1])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

\* Leader of the current view executes a pending RW transaction
RwTxExecuteAction ==
    \E tx \in TxIds :
        /\ IsRwRequest(tx)
        /\ ~HasResponse(tx)
        /\ ~TxInBranch(tx, LeaderBranch)
        /\ ledgerBranches' = [ledgerBranches EXCEPT ![CurrentView] =
                                Append(@, [view |-> CurrentView, tx |-> tx])]
        /\ UNCHANGED <<history, commitSeqNum>>

\* The leader of some view replies to an executed RW transaction
RwTxResponseAction ==
    \E v \in 1..CurrentView :
      \E i \in 1..Len(ledgerBranches[v]) :
        LET e == ledgerBranches[v][i] IN
        /\ e.view = v
        /\ ~HasResponse(e.tx)
        /\ history' = Append(history,
                        [type     |-> RwTxResponse,
                         tx       |-> e.tx,
                         observed |-> ObservedPrefix(ledgerBranches[v], i),
                         tx_id    |-> <<v, i>>])
        /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

\* Replication reaches quorum: the commit index advances
AdvanceCommitAction ==
    \E i \in (commitSeqNum + 1)..Len(LeaderBranch) :
        /\ commitSeqNum' = i
        /\ UNCHANGED <<history, ledgerBranches>>

\* Election: a new view starts. The new leader's ledger is a prefix of the
\* old leader's ledger that contains every committed entry.
ElectionAction ==
    /\ CurrentView < MaxViews
    /\ \E i \in commitSeqNum..Len(LeaderBranch) :
        ledgerBranches' = Append(ledgerBranches, SubSeq(LeaderBranch, 1, i))
    /\ UNCHANGED <<history, commitSeqNum>>

\* Client learns the status of a transaction ID it was given
StatusCommittedResponseAction ==
    \E txid \in ResponseTxIds :
        /\ txid[2] >= 1
        /\ ~HasStatus(txid, CommittedStatus)
        /\ IsCommittedTxId(txid)
        /\ history' = Append(history,
                        [type |-> TxStatusReceived, tx_id |-> txid,
                         status |-> CommittedStatus])
        /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

StatusInvalidResponseAction ==
    \E txid \in ResponseTxIds :
        /\ txid[2] >= 1
        /\ ~HasStatus(txid, InvalidStatus)
        /\ IsInvalidTxId(txid)
        /\ history' = Append(history,
                        [type |-> TxStatusReceived, tx_id |-> txid,
                         status |-> InvalidStatus])
        /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

MultiNodeActions ==
    \/ RwTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ AdvanceCommitAction
    \/ ElectionAction
    \/ StatusCommittedResponseAction
    \/ StatusInvalidResponseAction

-----------------------------------------------------------------------------
(* Read-only transaction actions *)

\* Client submits a read-only transaction
RoTxRequestAction ==
    /\ NumRequests < MaxRequests
    /\ history' = Append(history,
                    [type |-> RoTxRequest, tx |-> NumRequests + 1])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

\* Some node (the leader of view v, which may be stale) serves the read.
\* It reads a prefix of length i of its ledger, using single-node read
\* semantics. The transaction ID is the position of the last write the
\* read observed.
RoTxResponseAction ==
    \E tx \in TxIds :
        /\ IsRoRequest(tx)
        /\ ~HasResponse(tx)
        /\ \E v \in 1..CurrentView :
             \E i \in 0..Len(ledgerBranches[v]) :
               LET tid == IF i = 0 THEN <<v, 0>>
                          ELSE <<ledgerBranches[v][i].view, i>>
               IN history' = Append(history,
                        [type     |-> RoTxResponse,
                         tx       |-> tx,
                         observed |-> ObservedPrefix(ledgerBranches[v], i),
                         tx_id    |-> tid])
        /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

-----------------------------------------------------------------------------
(* Specification *)

Next ==
    \/ MultiNodeActions
    \/ RoTxRequestAction
    \/ RoTxResponseAction

Fairness ==
    /\ WF_vars(RoTxResponseAction)
    /\ WF_vars(RwTxExecuteAction)
    /\ WF_vars(RwTxResponseAction)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety invariants *)

TypeOK ==
    /\ history \in Seq([type : {RwTxRequest, RoTxRequest}, tx : TxIds]
                       \cup [type : {RwTxResponse, RoTxResponse}, tx : TxIds,
                             observed : Seq(TxIds),
                             tx_id : Views \X Nat]
                       \cup [type : {TxStatusReceived},
                             tx_id : Views \X Nat,
                             status : {CommittedStatus, InvalidStatus}])
    /\ ledgerBranches \in Seq(Seq([view : Views, tx : TxIds]))
    /\ CurrentView \in Views
    /\ commitSeqNum \in 0..Len(LeaderBranch)

\* Each request receives at most one response
AtMostOneResponseInv ==
    \A i, j \in DOMAIN history :
        ( /\ history[i].type \in {RwTxResponse, RoTxResponse}
          /\ history[j].type \in {RwTxResponse, RoTxResponse}
          /\ history[i].tx = history[j].tx ) => i = j

\* Each response answers a request that came earlier
ResponseFollowsRequestInv ==
    \A i \in DOMAIN history :
        /\ history[i].type = RwTxResponse =>
              \E j \in 1..(i-1) : history[j].type = RwTxRequest
                                   /\ history[j].tx = history[i].tx
        /\ history[i].type = RoTxResponse =>
              \E j \in 1..(i-1) : history[j].type = RoTxRequest
                                   /\ history[j].tx = history[i].tx

\* Each transaction appears at most once in any ledger branch
UniqueTxsInBranchesInv ==
    \A v \in DOMAIN ledgerBranches :
        \A a, b \in 1..Len(ledgerBranches[v]) :
            ledgerBranches[v][a].tx = ledgerBranches[v][b].tx => a = b

\* Only read-write transactions are written to the ledger
OnlyRwTxsInLedgerInv ==
    \A v \in DOMAIN ledgerBranches :
        \A k \in 1..Len(ledgerBranches[v]) : IsRwRequest(ledgerBranches[v][k].tx)

\* A transaction ID is never reported as both committed and invalid
NoConflictingStatusInv ==
    \A i, j \in DOMAIN history :
        ( /\ history[i].type = TxStatusReceived
          /\ history[j].type = TxStatusReceived
          /\ history[i].tx_id = history[j].tx_id )
        => history[i].status = history[j].status

\* A reported-committed transaction ID really is in the committed ledger
CommittedStatusIsCommittedInv ==
    \A i \in DOMAIN history :
        ( history[i].type = TxStatusReceived /\ history[i].status = CommittedStatus )
        => IsCommittedTxId(history[i].tx_id)

\* Committed RW transactions observed exactly a prefix of the committed ledger
CommittedRwSerializableInv ==
    \A i \in DOMAIN history :
        ( /\ history[i].type = RwTxResponse
          /\ IsCommittedTxId(history[i].tx_id) )
        => history[i].observed = ObservedPrefix(CommittedLedger, history[i].tx_id[2])

\* Committed RO transactions observed a coherent, committed prefix of data.
\* That prefix is a consistent snapshot across all nodes.
CommittedRoSerializableInv ==
    \A i \in DOMAIN history :
        ( /\ history[i].type = RoTxResponse
          /\ history[i].tx_id[2] >= 1
          /\ IsCommittedTxId(history[i].tx_id) )
        => history[i].observed = ObservedPrefix(CommittedLedger, history[i].tx_id[2])

\* Every read observes a snapshot that some single node actually held.
\* The snapshot is a prefix of a real ledger branch.
RoObservesSomeBranchPrefixInv ==
    \A i \in DOMAIN history :
        history[i].type = RoTxResponse =>
            \E v \in DOMAIN ledgerBranches :
                /\ Len(history[i].observed) <= Len(ledgerBranches[v])
                /\ history[i].observed =
                     ObservedPrefix(ledgerBranches[v], Len(history[i].observed))

\* Bounded state space
BoundedInv ==
    /\ NumRequests <= MaxRequests
    /\ CurrentView <= MaxViews

-----------------------------------------------------------------------------
(* Temporal properties *)

\* The committed ledger only grows
CommittedLedgerAppendOnly ==
    [][ /\ Len(CommittedLedger') >= Len(CommittedLedger)
        /\ SubSeq(CommittedLedger', 1, Len(CommittedLedger)) = CommittedLedger
      ]_vars

\* Every read-only request is eventually answered
RoTxEventuallyResponded ==
    \A tx \in TxIds : IsRoRequest(tx) ~> HasResponse(tx)

\* Once a response has been given, it is never withdrawn
ResponsesStable ==
    \A tx \in TxIds : [](HasResponse(tx) => []HasResponse(tx))

=============================================================================