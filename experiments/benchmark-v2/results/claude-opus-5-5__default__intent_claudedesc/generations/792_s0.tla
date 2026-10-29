--------------------------- MODULE KeyValueStore ---------------------------
(***************************************************************************)
(* A transactional key-value store with snapshot isolation.                *)
(*                                                                         *)
(* Each transaction opens with a private snapshot of the store. Reads and  *)
(* writes go to that snapshot. On commit, the transaction's writes are     *)
(* installed in the store. A commit is rejected (write-write conflict      *)
(* detection) if another transaction committed a write to the same key     *)
(* after this transaction's snapshot was taken.                            *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    Key,        \* The set of all keys.
    Val,        \* The set of all values.
    TxId,       \* The set of all transaction IDs (symmetric).
    NoVal       \* Model value representing an empty/unset key.

ASSUME NoVal \notin Val

VARIABLES
    store,          \* The committed key-value store.
    tx,             \* The set of currently open transactions.
    snapshotStore,  \* Each transaction's private snapshot of the store.
    written,        \* Keys written by each transaction.
    missed          \* Writes committed by others that each transaction cannot see.

vars == <<store, tx, snapshotStore, written, missed>>

Store == [Key -> Val \cup {NoVal}]

-----------------------------------------------------------------------------
(* Type correctness *)

TypeInvariant ==
    /\ store \in Store
    /\ tx \subseteq TxId
    /\ snapshotStore \in [TxId -> Store]
    /\ written \in [TxId -> SUBSET Key]
    /\ missed \in [TxId -> SUBSET Key]

-----------------------------------------------------------------------------
(* Safety invariants *)

\* Visibility of committed changes: an open transaction's snapshot matches
\* the committed store on every key, except keys it wrote itself and keys
\* that other transactions committed after it took its snapshot.
CommittedVisibility ==
    \A t \in tx : \A k \in Key :
        (store[k] /= snapshotStore[t][k] /\ k \notin written[t])
            => k \in missed[t]

\* Isolation: a transaction that is not open has no snapshot state, no
\* writes, and no missed writes. Only the transaction itself writes to its
\* snapshot, so other transactions never see its partial effects.
Isolation ==
    \A t \in TxId \ tx :
        /\ \A k \in Key : snapshotStore[t][k] = NoVal
        /\ written[t] = {}
        /\ missed[t] = {}

\* Missed and written keys always belong to open transactions.
TxStateConsistency ==
    \A t \in TxId :
        (written[t] /= {} \/ missed[t] /= {}) => t \in tx

\* Consistency of stored data: every key either holds a value or is unset.
StoreConsistency ==
    \A k \in Key : store[k] \in Val \cup {NoVal}

TxLifecycle ==
    /\ CommittedVisibility
    /\ Isolation
    /\ TxStateConsistency

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ store = [k \in Key |-> NoVal]
    /\ tx = {}
    /\ snapshotStore = [t \in TxId |-> [k \in Key |-> NoVal]]
    /\ written = [t \in TxId |-> {}]
    /\ missed = [t \in TxId |-> {}]

-----------------------------------------------------------------------------
(* Actions *)

\* Open a new transaction: take a snapshot of the committed store.
OpenTx(t) ==
    /\ t \notin tx
    /\ tx' = tx \cup {t}
    /\ snapshotStore' = [snapshotStore EXCEPT ![t] = store]
    /\ UNCHANGED <<store, written, missed>>

\* Add a value to a key that is unset in the transaction's snapshot.
Add(t, k, v) ==
    /\ t \in tx
    /\ snapshotStore[t][k] = NoVal
    /\ snapshotStore' = [snapshotStore EXCEPT ![t][k] = v]
    /\ written' = [written EXCEPT ![t] = @ \cup {k}]
    /\ UNCHANGED <<store, tx, missed>>

\* Update the value of a key that is set in the transaction's snapshot.
Update(t, k, v) ==
    /\ t \in tx
    /\ snapshotStore[t][k] \notin {NoVal, v}
    /\ snapshotStore' = [snapshotStore EXCEPT ![t][k] = v]
    /\ written' = [written EXCEPT ![t] = @ \cup {k}]
    /\ UNCHANGED <<store, tx, missed>>

\* Remove a key from the transaction's snapshot.
Remove(t, k) ==
    /\ t \in tx
    /\ snapshotStore[t][k] /= NoVal
    /\ snapshotStore' = [snapshotStore EXCEPT ![t][k] = NoVal]
    /\ written' = [written EXCEPT ![t] = @ \cup {k}]
    /\ UNCHANGED <<store, tx, missed>>

\* Abort a transaction, discarding all of its changes.
RollbackTx(t) ==
    /\ t \in tx
    /\ tx' = tx \ {t}
    /\ snapshotStore' = [snapshotStore EXCEPT ![t] = [k \in Key |-> NoVal]]
    /\ written' = [written EXCEPT ![t] = {}]
    /\ missed' = [missed EXCEPT ![t] = {}]
    /\ UNCHANGED store

\* Commit a transaction if it has no write-write conflict. Its writes are
\* installed atomically, and every other open transaction records them as
\* missed because its snapshot predates this commit.
CloseTx(t) ==
    /\ t \in tx
    /\ missed[t] \cap written[t] = {}
    /\ store' = [k \in Key |->
                    IF k \in written[t] THEN snapshotStore[t][k] ELSE store[k]]
    /\ tx' = tx \ {t}
    /\ missed' = [otherTx \in TxId |->
                    IF otherTx \in tx' THEN missed[otherTx] \cup written[t]
                    ELSE {}]
    /\ snapshotStore' = [snapshotStore EXCEPT ![t] = [k \in Key |-> NoVal]]
    /\ written' = [written EXCEPT ![t] = {}]

-----------------------------------------------------------------------------
(* Specification *)

Next ==
    \/ \E t \in TxId : OpenTx(t)
    \/ \E t \in TxId : \E k \in Key : \E v \in Val : Add(t, k, v)
    \/ \E t \in TxId : \E k \in Key : \E v \in Val : Update(t, k, v)
    \/ \E t \in TxId : \E k \in Key : Remove(t, k)
    \/ \E t \in TxId : RollbackTx(t)
    \/ \E t \in TxId : CloseTx(t)

Fairness ==
    \A t \in TxId : WF_vars(RollbackTx(t) \/ CloseTx(t))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Liveness *)

\* Every open transaction is eventually committed or rolled back.
TxEventuallyEnds ==
    \A t \in TxId : (t \in tx) ~> (t \notin tx)

-----------------------------------------------------------------------------
(* Model checking support *)

\* Transaction IDs are interchangeable.
Symmetry == Permutations(TxId)

-----------------------------------------------------------------------------
THEOREM Spec => [](TypeInvariant /\ TxLifecycle /\ StoreConsistency)
THEOREM Spec => TxEventuallyEnds
=============================================================================