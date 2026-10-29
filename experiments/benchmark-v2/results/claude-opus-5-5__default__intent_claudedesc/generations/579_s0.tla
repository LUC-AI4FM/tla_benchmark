------------------------------ MODULE MultiNodeConsensus ------------------------------
(***************************************************************************)
(* Multi-node consensus / replicated ledger specification.                 *)
(*                                                                         *)
(* The first part ("single-node layer") is the client-observable ledger    *)
(* and history model: clients submit read/write transactions, the leader   *)
(* executes them into the ledger, and clients receive transaction ids and  *)
(* status responses (Committed or Invalid). The ledger is a sequence of    *)
(* branches, one per view. A view change starts a new branch, which may be *)
(* a truncation of the previous branch.                                    *)
(*                                                                         *)
(* The second part ("multi-node layer") composes this with replication     *)
(* across Nodes. Each node keeps a local log. A leader replicates entries  *)
(* to followers, which may truncate conflicting suffixes. Commitment       *)
(* needs a quorum. A view change elects a sufficiently up-to-date node,    *)
(* and its log becomes the new branch.                                     *)
(*                                                                         *)
(* Bounded versions limit the number of view changes (ViewLimit) and the   *)
(* length of the history (HistoryLimit) for model checking.                *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Nodes,          \* set of node identifiers
    ViewLimit,      \* maximum view number (bounds the number of view changes)
    HistoryLimit    \* maximum length of the client-observable history

ASSUME Nodes # {}
ASSUME ViewLimit \in Nat \ {0}
ASSUME HistoryLimit \in Nat

VARIABLES
    history,        \* sequence of client-observable events
    ledgerBranches, \* ledgerBranches[v] is the leader's ledger during view v
    view,           \* current view number
    leader,         \* leader of the current view
    nodeLog,        \* nodeLog[n] is the local ledger of node n
    commitIndex     \* length of the committed prefix of the current branch

vars == <<history, ledgerBranches, view, leader, nodeLog, commitIndex>>

-----------------------------------------------------------------------------
(* Helpers *)

Min(a, b) == IF a <= b THEN a ELSE b

IsPrefix(s, t) == Len(s) <= Len(t) /\ SubSeq(t, 1, Len(s)) = s

\* Length of the longest common prefix of two sequences
LCP(a, b) ==
    LET m == Min(Len(a), Len(b))
    IN CHOOSE k \in 0..m :
          /\ SubSeq(a, 1, k) = SubSeq(b, 1, k)
          /\ (k = m \/ a[k+1] # b[k+1])

Quorums == { Q \in SUBSET Nodes : 2 * Cardinality(Q) > Cardinality(Nodes) }

LastView(log) == IF log = <<>> THEN 0 ELSE log[Len(log)].view

\* Log a is at least as up-to-date as log b
UpToDate(a, b) ==
    \/ LastView(a) > LastView(b)
    \/ /\ LastView(a) = LastView(b)
       /\ Len(a) >= Len(b)

NoTxId == <<0, 0>>

Event(type, tx, txid, status) ==
    [type |-> type, tx |-> tx, tx_id |-> txid, status |-> status]

Entries == [view : Nat, tx : Nat]

EventTypes == {"RwTxRequest", "RwTxResponse", "TxStatusReceived"}
Statuses   == {"None", "CommittedStatus", "InvalidStatus"}

-----------------------------------------------------------------------------
(* Single-node layer: ledger branches and client history *)

\* The current ledger branch (the leader's ledger in the current view)
Latest == ledgerBranches[Len(ledgerBranches)]

CommittedPrefix == SubSeq(Latest, 1, commitIndex)

RequestedTxs ==
    { history[i].tx : i \in { j \in DOMAIN history :
                                 history[j].type = "RwTxRequest" } }

TxsInLog(log) == { log[i].tx : i \in DOMAIN log }

ResponseEvents ==
    { history[i] : i \in { j \in DOMAIN history :
                              history[j].type = "RwTxResponse" } }

StatusEvents ==
    { history[i] : i \in { j \in DOMAIN history :
                              history[j].type = "TxStatusReceived" } }

\* tx_id <<v, i>> is committed in the current branch
IsCommitted(txid) ==
    LET v == txid[1]
        i == txid[2]
    IN /\ i >= 1
       /\ i <= commitIndex
       /\ Latest[i].view = v

\* tx_id <<v, i>> can never commit
IsInvalid(txid) ==
    LET v == txid[1]
        i == txid[2]
    IN \/ /\ i >= 1
          /\ i <= commitIndex
          /\ Latest[i].view # v
       \/ \E j \in 1..Min(i, commitIndex) : Latest[j].view > v

\* A client submits a new read/write transaction with a fresh identifier
RwTxRequest ==
    /\ history' = Append(history,
                         Event("RwTxRequest", Len(history) + 1, NoTxId, "None"))
    /\ UNCHANGED <<ledgerBranches, view, leader, nodeLog, commitIndex>>

\* The leader executes a requested transaction and appends it to its ledger
ExecuteTx(t) ==
    /\ t \in RequestedTxs
    /\ t \notin TxsInLog(nodeLog[leader])
    /\ LET e == [view |-> view, tx |-> t]
       IN /\ nodeLog' = [nodeLog EXCEPT ![leader] = Append(@, e)]
          /\ ledgerBranches' =
                [ledgerBranches EXCEPT ![Len(ledgerBranches)] = Append(@, e)]
    /\ UNCHANGED <<history, view, leader, commitIndex>>

\* The leader returns a transaction id for an executed transaction
RwTxResponse(i) ==
    /\ i \in DOMAIN Latest
    /\ Latest[i].view = view
    /\ LET txid == <<Latest[i].view, i>>
       IN /\ \A e \in ResponseEvents : e.tx_id # txid
          /\ history' = Append(history,
                               Event("RwTxResponse", Latest[i].tx, txid, "None"))
    /\ UNCHANGED <<ledgerBranches, view, leader, nodeLog, commitIndex>>

\* A status query reports that a transaction is committed
StatusCommittedResponse(e) ==
    /\ e \in ResponseEvents
    /\ IsCommitted(e.tx_id)
    /\ LET ev == Event("TxStatusReceived", e.tx, e.tx_id, "CommittedStatus")
       IN /\ ev \notin StatusEvents
          /\ history' = Append(history, ev)
    /\ UNCHANGED <<ledgerBranches, view, leader, nodeLog, commitIndex>>

\* A status query reports that a transaction is invalid
\* (it was lost in a view change and can never commit)
StatusInvalidResponse(e) ==
    /\ e \in ResponseEvents
    /\ IsInvalid(e.tx_id)
    /\ LET ev == Event("TxStatusReceived", e.tx, e.tx_id, "InvalidStatus")
       IN /\ ev \notin StatusEvents
          /\ history' = Append(history, ev)
    /\ UNCHANGED <<ledgerBranches, view, leader, nodeLog, commitIndex>>

-----------------------------------------------------------------------------
(* Multi-node layer: replication, quorum commit, view change *)

\* The leader replicates a prefix of its log (length j) to follower m.
\* A follower truncates its log if it conflicts with the leader's log.
Replicate(m, j) ==
    LET L == nodeLog[leader]
        F == nodeLog[m]
        k == LCP(F, L)
    IN /\ m # leader
       /\ j \in k..Len(L)
       /\ \/ j >= Len(F)       \* extends a consistent log
          \/ k < Len(F)        \* or replaces a conflicting suffix
       /\ nodeLog' = [nodeLog EXCEPT ![m] = SubSeq(L, 1, j)]
       /\ UNCHANGED <<history, ledgerBranches, view, leader, commitIndex>>

\* The leader advances the commit index once a quorum stores an entry
\* from the current view at index i.
AdvanceCommit(i) ==
    LET L == nodeLog[leader]
    IN /\ i > commitIndex
       /\ i <= Len(L)
       /\ L[i].view = view
       /\ { n \in Nodes : Len(nodeLog[n]) >= i /\ nodeLog[n][i] = L[i] }
            \in Quorums
       /\ commitIndex' = i
       /\ UNCHANGED <<history, ledgerBranches, view, leader, nodeLog>>

\* View change: node n becomes leader of the next view, backed by a quorum
\* whose logs are no more up-to-date than n's. The new branch is n's log,
\* which may truncate the uncommitted suffix of the previous branch.
ViewChange(n) ==
    /\ \E Q \in Quorums :
          /\ n \in Q
          /\ \A m \in Q : UpToDate(nodeLog[n], nodeLog[m])
    /\ view' = view + 1
    /\ leader' = n
    /\ ledgerBranches' = Append(ledgerBranches, nodeLog[n])
    /\ UNCHANGED <<history, nodeLog, commitIndex>>

-----------------------------------------------------------------------------
(* Initial state and next-state relations *)

Init ==
    /\ history = <<>>
    /\ ledgerBranches = << <<>> >>
    /\ view = 1
    /\ leader \in Nodes
    /\ nodeLog = [n \in Nodes |-> <<>>]
    /\ commitIndex = 0

\* Actions that append to the client history
HistoryNext ==
    \/ RwTxRequest
    \/ \E i \in DOMAIN Latest : RwTxResponse(i)
    \/ \E e \in ResponseEvents : StatusCommittedResponse(e)
    \/ \E e \in ResponseEvents : StatusInvalidResponse(e)

\* Actions that do not append to the history
LedgerNext ==
    \/ \E t \in RequestedTxs : ExecuteTx(t)
    \/ \E m \in Nodes, j \in 0..Len(nodeLog[leader]) : Replicate(m, j)
    \/ \E i \in 1..Len(nodeLog[leader]) : AdvanceCommit(i)

ViewChangeNext == \E n \in Nodes : ViewChange(n)

\* Unbounded next-state relation
Next ==
    \/ HistoryNext
    \/ LedgerNext
    \/ ViewChangeNext

\* Bounded next-state relation for model checking
BoundedNext ==
    \/ Len(history) < HistoryLimit /\ HistoryNext
    \/ LedgerNext
    \/ view < ViewLimit /\ ViewChangeNext

UnboundedSpec == Init /\ [][Next]_vars

Spec == Init /\ [][BoundedNext]_vars

\* Optional state constraints when checking UnboundedSpec
ViewLimitConstraint    == view <= ViewLimit
HistoryLimitConstraint == Len(history) <= HistoryLimit

-----------------------------------------------------------------------------
(* Safety invariants *)

TypeOK ==
    /\ history \in Seq([type : EventTypes, tx : Nat,
                        tx_id : Nat \X Nat, status : Statuses])
    /\ ledgerBranches \in Seq(Seq(Entries))
    /\ view \in Nat \ {0}
    /\ leader \in Nodes
    /\ nodeLog \in [Nodes -> Seq(Entries)]
    /\ commitIndex \in Nat

\* One ledger branch per view, and the current branch is the leader's log
BranchPerView ==
    /\ Len(ledgerBranches) = view
    /\ Latest = nodeLog[leader]

\* The committed prefix is within the current branch
CommitWithinLedger == commitIndex <= Len(Latest)

\* A transaction id is never reported both committed and invalid
CommittedInvalidExclusive ==
    \A e1, e2 \in StatusEvents :
        e1.tx_id = e2.tx_id => e1.status = e2.status

\* Every transaction reported committed is still committed in the current branch
CommittedStatusDurable ==
    \A e \in StatusEvents :
        e.status = "CommittedStatus" => IsCommitted(e.tx_id)

\* Every transaction reported invalid is still invalid
InvalidStatusDurable ==
    \A e \in StatusEvents :
        e.status = "InvalidStatus" => IsInvalid(e.tx_id)

\* Every committed entry is held by a quorum of nodes
CommittedOnQuorum ==
    commitIndex > 0 =>
        { n \in Nodes : IsPrefix(CommittedPrefix, nodeLog[n]) } \in Quorums

\* Log matching: equal entries at the same index imply equal prefixes
LogMatching ==
    \A n, m \in Nodes :
        \A i \in (DOMAIN nodeLog[n]) \cap (DOMAIN nodeLog[m]) :
            nodeLog[n][i] = nodeLog[m][i] =>
                SubSeq(nodeLog[n], 1, i) = SubSeq(nodeLog[m], 1, i)

\* Views never decrease along any log, and never exceed the current view
ViewsMonotonicInLogs ==
    \A n \in Nodes :
        \A i, j \in DOMAIN nodeLog[n] :
            /\ i < j => nodeLog[n][i].view <= nodeLog[n][j].view
            /\ nodeLog[n][i].view <= view

\* No transaction appears twice in the current branch
NoDuplicateTxInLedger ==
    \A i, j \in DOMAIN Latest : i # j => Latest[i].tx # Latest[j].tx

\* Every ledger branch extends the committed prefix that existed when it began.
\* In particular, the current branch contains the whole committed prefix.
LeaderHasCommitted == IsPrefix(CommittedPrefix, nodeLog[leader])

Safety ==
    /\ TypeOK
    /\ BranchPerView
    /\ CommitWithinLedger
    /\ CommittedInvalidExclusive
    /\ CommittedStatusDurable
    /\ InvalidStatusDurable
    /\ CommittedOnQuorum
    /\ LogMatching
    /\ ViewsMonotonicInLogs
    /\ NoDuplicateTxInLedger
    /\ LeaderHasCommitted

-----------------------------------------------------------------------------
(* Temporal (action) safety properties *)

\* The committed ledger only grows: view changes never truncate committed entries
CommittedPrefixMonotonic ==
    [][IsPrefix(CommittedPrefix, CommittedPrefix')]_vars

\* The history is append-only
HistoryAppendOnly ==
    [][IsPrefix(history, history')]_vars

\* Past ledger branches are immutable; only the current branch may grow
BranchesImmutable ==
    [][ /\ Len(ledgerBranches) <= Len(ledgerBranches')
        /\ \A b \in 1..(Len(ledgerBranches) - 1) :
              ledgerBranches'[b] = ledgerBranches[b] ]_vars

THEOREM Spec => []Safety
=============================================================================