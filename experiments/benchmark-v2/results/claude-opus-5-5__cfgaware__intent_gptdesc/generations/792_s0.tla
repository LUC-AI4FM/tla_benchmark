------------------------------ MODULE SnapshotKV ------------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Key, TxId, NoVal

ASSUME NoVal \notin TxId

\* A transaction writes its own identifier as the value. This keeps the value
\* domain finite and makes every committed value traceable to its writer.
Val == TxId \cup {NoVal}

VARIABLES
    store,      \* committed key-value mapping (the replicated state, abstractly)
    txState,    \* lifecycle of each transaction
    snapshot,   \* per-transaction snapshot of committed store taken at Begin
    written,    \* per-transaction write buffer (set of keys written)
    startIdx,   \* number of committed transactions visible at Begin
    commitLog,  \* sequence of committed transactions, in commit order
    txReads,    \* observations made by transactional reads <<t, k, v>>
    ntReads     \* observations made by non-transactional reads <<k, v, n>>

vars == <<store, txState, snapshot, written, startIdx, commitLog, txReads, ntReads>>

TxStates == {"init", "active", "committed", "aborted"}

-----------------------------------------------------------------------------
\* Helper operators

MaxOf(S) == CHOOSE i \in S : \A j \in S : j <= i

\* The committed value of key k after the first n commits in commitLog.
ValAfter(n, k) ==
    LET W == {i \in 1..n : k \in written[commitLog[i]]}
    IN IF W = {} THEN NoVal ELSE commitLog[MaxOf(W)]

\* The value a transaction t observes for key k: its own write, if any,
\* otherwise the value in its start snapshot.
TxView(t, k) == IF k \in written[t] THEN t ELSE snapshot[t][k]

\* t conflicts if some transaction that committed after t began wrote a key
\* that t also wrote (first-committer-wins).
Conflict(t) ==
    \E i \in (startIdx[t] + 1)..Len(commitLog) :
        written[commitLog[i]] \cap written[t] # {}

-----------------------------------------------------------------------------
TypeOK ==
    /\ store \in [Key -> Val]
    /\ txState \in [TxId -> TxStates]
    /\ snapshot \in [TxId -> [Key -> Val]]
    /\ written \in [TxId -> SUBSET Key]
    /\ startIdx \in [TxId -> 0..Cardinality(TxId)]
    /\ commitLog \in Seq(TxId)
    /\ Len(commitLog) <= Cardinality(TxId)
    /\ txReads \subseteq (TxId \X Key \X Val)
    /\ ntReads \subseteq (Key \X Val \X (0..Cardinality(TxId)))

Init ==
    /\ store = [k \in Key |-> NoVal]
    /\ txState = [t \in TxId |-> "init"]
    /\ snapshot = [t \in TxId |-> [k \in Key |-> NoVal]]
    /\ written = [t \in TxId |-> {}]
    /\ startIdx = [t \in TxId |-> 0]
    /\ commitLog = <<>>
    /\ txReads = {}
    /\ ntReads = {}

-----------------------------------------------------------------------------
\* Transitions

\* Start a transaction: it takes a snapshot of the committed state.
Begin(t) ==
    /\ txState[t] = "init"
    /\ txState' = [txState EXCEPT ![t] = "active"]
    /\ snapshot' = [snapshot EXCEPT ![t] = store]
    /\ startIdx' = [startIdx EXCEPT ![t] = Len(commitLog)]
    /\ UNCHANGED <<store, written, commitLog, txReads, ntReads>>

\* A transactional read sees the snapshot plus the transaction's own writes.
TxRead(t, k) ==
    /\ txState[t] = "active"
    /\ txReads' = txReads \cup {<<t, k, TxView(t, k)>>}
    /\ UNCHANGED <<store, txState, snapshot, written, startIdx, commitLog, ntReads>>

\* A transactional write goes only into the transaction-local buffer.
TxWrite(t, k) ==
    /\ txState[t] = "active"
    /\ k \notin written[t]
    /\ written' = [written EXCEPT ![t] = @ \cup {k}]
    /\ UNCHANGED <<store, txState, snapshot, startIdx, commitLog, txReads, ntReads>>

\* Commit atomically installs every buffered write. It is allowed only when
\* there is no write-write conflict with a concurrent committed transaction.
Commit(t) ==
    /\ txState[t] = "active"
    /\ ~Conflict(t)
    /\ txState' = [txState EXCEPT ![t] = "committed"]
    /\ store' = [k \in Key |-> IF k \in written[t] THEN t ELSE store[k]]
    /\ commitLog' = Append(commitLog, t)
    /\ UNCHANGED <<snapshot, written, startIdx, txReads, ntReads>>

\* Abort discards the buffered writes. It may happen at any time while the
\* transaction is active, and it is the only option once a conflict exists.
Abort(t) ==
    /\ txState[t] = "active"
    /\ txState' = [txState EXCEPT ![t] = "aborted"]
    /\ UNCHANGED <<store, snapshot, written, startIdx, commitLog, txReads, ntReads>>

\* A non-transactional read observes the current committed state.
\* (A non-transactional write is modeled as a single-key transaction:
\*  Begin, TxWrite, Commit.)
NTRead(k) ==
    /\ ntReads' = ntReads \cup {<<k, store[k], Len(commitLog)>>}
    /\ UNCHANGED <<store, txState, snapshot, written, startIdx, commitLog, txReads>>

\* Once every transaction has finished, the system idles. This is not a deadlock.
Done ==
    /\ \A t \in TxId : txState[t] \in {"committed", "aborted"}
    /\ UNCHANGED vars

Next ==
    \/ \E t \in TxId :
         \/ Begin(t)
         \/ Commit(t)
         \/ Abort(t)
         \/ \E k \in Key : TxRead(t, k) \/ TxWrite(t, k)
    \/ \E k \in Key : NTRead(k)
    \/ Done

Fairness ==
    \A t \in TxId :
        /\ WF_vars(Begin(t))
        /\ SF_vars(Commit(t))
        /\ WF_vars(Abort(t))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety properties (invariants / assertions)

\* (1) Every started transaction's snapshot is exactly the committed state
\*     after some prefix of the commit order. Its reads are consistent with
\*     that snapshot plus its own writes.
SnapshotConsistency ==
    /\ \A t \in TxId :
         txState[t] # "init" =>
            /\ startIdx[t] <= Len(commitLog)
            /\ \A k \in Key : snapshot[t][k] = ValAfter(startIdx[t], k)
    /\ \A r \in txReads :
         r[3] = r[1] \/ r[3] = snapshot[r[1]][r[2]]

\* (2) Atomic visibility: the store is the result of applying the full write
\*     sets of the committed transactions, in commit order, with nothing
\*     partial and nothing from aborted or active transactions.
AtomicVisibility ==
    /\ \A k \in Key : store[k] = ValAfter(Len(commitLog), k)
    /\ \A i \in 1..Len(commitLog) : txState[commitLog[i]] = "committed"
    /\ \A t \in TxId : txState[t] = "committed" <=>
                         \E i \in 1..Len(commitLog) : commitLog[i] = t
    /\ \A i, j \in 1..Len(commitLog) : i # j => commitLog[i] # commitLog[j]

\* (3) Write-conflict prevention: two committed transactions whose intervals
\*     overlap have disjoint write sets.
NoWriteConflict ==
    \A i, j \in 1..Len(commitLog) :
        (i < j /\ startIdx[commitLog[j]] < i) =>
            written[commitLog[i]] \cap written[commitLog[j]] = {}

\* (4) Non-transactional reads always return the committed value as of the
\*     time they were performed.
NonTxConsistency ==
    \A r \in ntReads : r[2] = ValAfter(r[3], r[1])

SnapshotIsolation ==
    /\ SnapshotConsistency
    /\ AtomicVisibility
    /\ NoWriteConflict
    /\ NonTxConsistency

-----------------------------------------------------------------------------
\* Liveness properties

\* Every transaction eventually finishes (commits or aborts). Under fair
\* scheduling the system therefore never gets stuck.
Termination ==
    <>(\A t \in TxId : txState[t] \in {"committed", "aborted"})

\* A transaction whose commit stays repeatedly enabled (i.e. it has no
\* conflict) eventually leaves the active state.
NonConflictingProgress ==
    \A t \in TxId :
        ([]<>(txState[t] = "active" /\ ~Conflict(t))) ~> (txState[t] # "active")

-----------------------------------------------------------------------------
\* Symmetry reduction over transaction identifiers
TxIdSymmetric == Permutations(TxId)

THEOREM Spec => []TypeOK
THEOREM Spec => []SnapshotIsolation
=============================================================================