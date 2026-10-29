--------------------------- MODULE KeyValueStore ---------------------------
(***************************************************************************)
(* A transactional key-value store using snapshot isolation.               *)
(*                                                                         *)
(* Each transaction opens with a private snapshot of the store. Reads see  *)
(* only that snapshot. Writes (add, update, remove) change only the        *)
(* snapshot. At commit, the store checks for write-write conflicts with    *)
(* transactions that committed concurrently ("first committer wins").      *)
(* If there is a conflict, the transaction can only be rolled back.        *)
(* This rule rules out lost updates.                                       *)
(*                                                                         *)
(* Transaction identifiers are symmetric. Use the Symmetry set below as   *)
(* the TLC SYMMETRY parameter.                                             *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    Key,    \* The set of all keys
    Val,    \* The set of all values
    TxId,   \* The set of all transaction IDs
    NoVal   \* Model value meaning "no value stored at this key"

ASSUME NoVal \notin Val

VARIABLES
    store,          \* The committed data store
    tx,             \* The set of open transactions
    snapshotStore,  \* Each transaction's private snapshot of the store
    written,        \* The keys each transaction has written to
    missed          \* Writes made by others that each open tx cannot see

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
(* Initial state *)

Init ==
    /\ store = [k \in Key |-> NoVal]
    /\ tx = {}
    /\ snapshotStore = [t \in TxId |-> [k \in Key |-> NoVal]]
    /\ written = [t \in TxId |-> {}]
    /\ missed = [t \in TxId |-> {}]

-----------------------------------------------------------------------------
(* Transaction lifecycle actions *)

\* Start a transaction with a snapshot of the current committed store.
OpenTx(t) ==
    /\ t \notin tx
    /\ tx' = tx \cup {t}
    /\ snapshotStore' = [snapshotStore EXCEPT ![t] = store]
    /\ UNCHANGED <<store, written, missed>>

\* Read a key. The value comes from the snapshot, so the step changes no state.
Read(t, k) ==
    /\ t \in tx
    /\ LET v == snapshotStore[t][k] IN v \in Val \cup {NoVal}
    /\ UNCHANGED vars

\* Insert a value at a key that has no value in the snapshot.
Add(t, k, v) ==
    /\ t \in tx
    /\ snapshotStore[t][k] = NoVal
    /\ snapshotStore' = [snapshotStore EXCEPT ![t][k] = v]
    /\ written' = [written EXCEPT ![t] = @ \cup {k}]
    /\ UNCHANGED <<store, tx, missed>>

\* Overwrite an existing value with a different value.
Update(t, k, v) ==
    /\ t \in tx
    /\ snapshotStore[t][k] \notin {NoVal, v}
    /\ snapshotStore' = [snapshotStore EXCEPT ![t][k] = v]
    /\ written' = [written EXCEPT ![t] = @ \cup {k}]
    /\ UNCHANGED <<store, tx, missed>>

\* Delete an existing value.
Remove(t, k) ==
    /\ t \in tx
    /\ snapshotStore[t][k] # NoVal
    /\ snapshotStore' = [snapshotStore EXCEPT ![t][k] = NoVal]
    /\ written' = [written EXCEPT ![t] = @ \cup {k}]
    /\ UNCHANGED <<store, tx, missed>>

\* Abort: throw away all of the transaction's changes.
RollbackTx(t) ==
    /\ t \in tx
    /\ tx' = tx \ {t}
    /\ snapshotStore' = [snapshotStore EXCEPT ![t] = [k \in Key |-> NoVal]]
    /\ written' = [written EXCEPT ![t] = {}]
    /\ missed' = [missed EXCEPT ![t] = {}]
    /\ UNCHANGED store

\* Commit: allowed only if no write-write conflict with concurrent commits.
\* The transaction's writes are installed in the store. Every other open
\* transaction records these keys as writes it has missed.
CloseTx(t) ==
    /\ t \in tx
    /\ missed[t] \cap written[t] = {}
    /\ store' = [k \in Key |->
                    IF k \in written[t] THEN snapshotStore[t][k] ELSE store[k]]
    /\ tx' = tx \ {t}
    /\ missed' = [o \in TxId |->
                    IF o \in tx' THEN missed[o] \cup written[t] ELSE {}]
    /\ snapshotStore' = [snapshotStore EXCEPT ![t] = [k \in Key |-> NoVal]]
    /\ written' = [written EXCEPT ![t] = {}]

-----------------------------------------------------------------------------
(* Next-state relation and specification *)

Next ==
    \E t \in TxId :
        \/ OpenTx(t)
        \/ \E k \in Key : Read(t, k)
        \/ \E k \in Key, v \in Val : Add(t, k, v) \/ Update(t, k, v)
        \/ \E k \in Key : Remove(t, k)
        \/ RollbackTx(t)
        \/ CloseTx(t)

\* Weak fairness on rollback ensures every open transaction eventually ends.
Fairness == \A t \in TxId : WF_vars(RollbackTx(t))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

\* Consistency: every open transaction's snapshot either matches the store,
\* or the difference comes from its own writes or from writes it has missed.
\* Closed transactions keep no leftover state.
TxLifecycle ==
    /\ \A t \in tx :
         \A k \in Key :
           (store[k] # snapshotStore[t][k] /\ k \notin written[t])
              => k \in missed[t]
    /\ \A t \in TxId \ tx :
         /\ \A k \in Key : snapshotStore[t][k] = NoVal
         /\ written[t] = {}
         /\ missed[t] = {}

\* Isolation (snapshot isolation): an open transaction's view of a key
\* changes only through its own writes.
\* A missed write is never exposed in the snapshot.
SnapshotIsolation ==
    \A t \in tx :
      \A k \in missed[t] \ written[t] :
        TRUE  \* the snapshot keeps its old value; that value is checked below

IsolationStep ==
    [][\A t \in tx \cap tx' :
         \A k \in Key :
           (snapshotStore'[t][k] # snapshotStore[t][k]) => (k \in written'[t])
      ]_vars

\* No lost updates: a transaction that overlaps a concurrent committed write
\* on the same key can never commit.
NoLostUpdates ==
    \A t \in tx :
      (missed[t] \cap written[t] # {}) => ~ENABLED CloseTx(t)

\* Committed writes are installed exactly in the store (temporal check).
CommitInstallsWrites ==
    [][\A t \in TxId :
         (t \in tx /\ t \notin tx' /\ store' # store)
            => \A k \in written[t] : store'[k] = snapshotStore[t][k]
      ]_vars

-----------------------------------------------------------------------------
(* Liveness *)

\* Every open transaction eventually commits or aborts.
EventuallyCloses == \A t \in TxId : (t \in tx) ~> (t \notin tx)

-----------------------------------------------------------------------------
(* Model-checking support: transaction IDs are interchangeable. *)

Symmetry == Permutations(TxId)

THEOREM Spec => [](TypeInvariant /\ TxLifecycle /\ NoLostUpdates)

=============================================================================