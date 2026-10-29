--------------------------- MODULE KeyValueStore ---------------------------
(***************************************************************************)
(* A simple transactional key-value store providing snapshot isolation.    *)
(* Each transaction works on its own snapshot of the store, taken when     *)
(* the transaction starts. Its reads and writes go to that snapshot. On    *)
(* commit, its writes become visible in the shared store.                  *)
(*                                                                         *)
(* A transaction can only commit if no other transaction has committed a   *)
(* write to a key it also wrote since it started. This rule is            *)
(* first-committer-wins, and it means committed writes are never lost.     *)
(* A transaction may also abort at any time, which discards its writes.    *)
(***************************************************************************)
CONSTANTS
    Key,    \* The set of all keys.
    Val,    \* The set of all values.
    TxId    \* The set of all transaction IDs (symmetric).

VARIABLES
    store,          \* The data store, mapping keys to values.
    tx,             \* The set of open snapshot transactions.
    snapshotStore,  \* Snapshots of the store for each transaction.
    written,        \* A log of writes performed within each transaction.
    missed          \* The set of writes invisible to each transaction.

vars == <<store, tx, snapshotStore, written, missed>>

NoVal == CHOOSE v : v \notin Val

Store == [Key -> Val \cup {NoVal}]

\* Symmetry set for model checking over interchangeable transaction IDs.
TxIdSymmetry == Permutations(TxId)

-----------------------------------------------------------------------------

Init ==
    /\ store = [k \in Key |-> NoVal]
    /\ tx = {}
    /\ snapshotStore = [t \in TxId |-> [k \in Key |-> NoVal]]
    /\ written = [t \in TxId |-> {}]
    /\ missed = [t \in TxId |-> {}]

TypeInvariant ==
    /\ store \in Store
    /\ tx \subseteq TxId
    /\ snapshotStore \in [TxId -> Store]
    /\ written \in [TxId -> SUBSET Key]
    /\ missed \in [TxId -> SUBSET Key]

\* Consistency and lifecycle invariant:
\* - In an open transaction, a key whose snapshot value differs from the
\*   store and was not written by the transaction must be recorded as missed.
\* - Transactions that are not open hold no leftover state.
TxLifecycle ==
    /\ \A t \in tx :
        \A k \in Key :
            (store[k] /= snapshotStore[t][k] /\ k \notin written[t])
                => k \in missed[t]
    /\ \A t \in TxId \ tx :
        /\ \A k \in Key : snapshotStore[t][k] = NoVal
        /\ written[t] = {}
        /\ missed[t] = {}

-----------------------------------------------------------------------------

\* Open a new transaction, taking a snapshot of the store.
OpenTx(t) ==
    /\ t \notin tx
    /\ tx' = tx \cup {t}
    /\ snapshotStore' = [snapshotStore EXCEPT ![t] = store]
    /\ UNCHANGED <<written, missed, store>>

\* Using transaction t, add value v to the store under key k.
Add(t, k, v) ==
    /\ t \in tx
    /\ snapshotStore[t][k] = NoVal
    /\ snapshotStore' = [snapshotStore EXCEPT ![t][k] = v]
    /\ written' = [written EXCEPT ![t] = @ \cup {k}]
    /\ UNCHANGED <<tx, missed, store>>

\* Using transaction t, update the value associated with key k to v.
Update(t, k, v) ==
    /\ t \in tx
    /\ snapshotStore[t][k] \notin {NoVal, v}
    /\ snapshotStore' = [snapshotStore EXCEPT ![t][k] = v]
    /\ written' = [written EXCEPT ![t] = @ \cup {k}]
    /\ UNCHANGED <<tx, missed, store>>

\* Using transaction t, remove key k from the store.
Remove(t, k) ==
    /\ t \in tx
    /\ snapshotStore[t][k] /= NoVal
    /\ snapshotStore' = [snapshotStore EXCEPT ![t][k] = NoVal]
    /\ written' = [written EXCEPT ![t] = @ \cup {k}]
    /\ UNCHANGED <<tx, missed, store>>

\* Abort transaction t, discarding its snapshot and writes.
RollbackTx(t) ==
    /\ t \in tx
    /\ tx' = tx \ {t}
    /\ snapshotStore' = [snapshotStore EXCEPT ![t] = [k \in Key |-> NoVal]]
    /\ written' = [written EXCEPT ![t] = {}]
    /\ missed' = [missed EXCEPT ![t] = {}]
    /\ UNCHANGED store

\* Commit transaction t. This is only allowed if no write it made conflicts
\* with a write committed by another transaction since it started
\* (first-committer-wins). This rule prevents lost updates.
CloseTx(t) ==
    /\ t \in tx
    /\ missed[t] \cap written[t] = {}
    /\ store' = [k \in Key |->
                    IF k \in written[t]
                    THEN snapshotStore[t][k]
                    ELSE store[k]]
    /\ tx' = tx \ {t}
    /\ missed' = [otherTx \in TxId |->
                    IF otherTx \in tx \ {t}
                    THEN missed[otherTx] \cup written[t]
                    ELSE {}]
    /\ snapshotStore' = [snapshotStore EXCEPT ![t] = [k \in Key |-> NoVal]]
    /\ written' = [written EXCEPT ![t] = {}]

Next ==
    \/ \E t \in TxId : OpenTx(t)
    \/ \E t \in tx : \E k \in Key : \E v \in Val : Add(t, k, v)
    \/ \E t \in tx : \E k \in Key : \E v \in Val : Update(t, k, v)
    \/ \E t \in tx : \E k \in Key : Remove(t, k)
    \/ \E t \in tx : RollbackTx(t)
    \/ \E t \in tx : CloseTx(t)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

THEOREM Spec => [](TypeInvariant /\ TxLifecycle)

\* Permutations is defined in TLC; restate locally to stay self-contained.
=============================================================================