------------------------------- MODULE KVsnap -------------------------------
(***************************************************************************)
(* A key-value store with snapshot isolation.                              *)
(* Each transaction starts by taking a snapshot of the shared store, reads *)
(* from its private snapshot, and applies its writes to that snapshot.     *)
(* At commit time the store applies first-committer-wins: the transaction  *)
(* commits only if no key it writes was changed by a transaction that      *)
(* committed after its snapshot was taken. These are its "missed" writes.  *)
(* Otherwise the transaction aborts.                                       *)
(*                                                                         *)
(* SnapshotIsolation and Serialization follow the client-centric (Crooks   *)
(* et al.) definitions. They are evaluated over the committed transactions *)
(* and the values those transactions read.                                 *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANT Key            \* The set of all keys.

TxId  == {"t1", "t2", "t3"}       \* The set of all transaction ids.
NoVal == "NoVal"                  \* Initial value of every key.

Val == TxId \cup {NoVal}

VARIABLES
    store,          \* The shared data store.
    tx,             \* The set of currently open transactions.
    missed,         \* For each tx: keys written by others since its snapshot.
    pc,             \* Control state of each transaction.
    snapshotStore,  \* Private snapshot of each transaction.
    read_keys,      \* Keys each transaction reads.
    write_keys,     \* Keys each transaction writes.
    reads,          \* Values each transaction observed (meaningful on read_keys).
    committed       \* The set of committed transactions.

vars == << store, tx, missed, pc, snapshotStore, read_keys, write_keys,
           reads, committed >>

InitStore == [k \in Key |-> NoVal]

-----------------------------------------------------------------------------
Init ==
    /\ store = InitStore
    /\ tx = {}
    /\ missed = [t \in TxId |-> {}]
    /\ pc = [t \in TxId |-> "START"]
    /\ snapshotStore = [t \in TxId |-> InitStore]
    /\ read_keys \in [TxId -> SUBSET Key]
    /\ write_keys \in [TxId -> SUBSET Key]
    /\ reads = [t \in TxId |-> InitStore]
    /\ committed = {}

\* Begin: take a consistent snapshot of the store.
Start(t) ==
    /\ pc[t] = "START"
    /\ tx' = tx \cup {t}
    /\ snapshotStore' = [snapshotStore EXCEPT ![t] = store]
    /\ pc' = [pc EXCEPT ![t] = "READ"]
    /\ UNCHANGED << store, missed, read_keys, write_keys, reads, committed >>

\* Read phase: read keys from the private snapshot.
Read(t) ==
    /\ pc[t] = "READ"
    /\ reads' = [reads EXCEPT ![t] =
                    [k \in Key |-> IF k \in read_keys[t]
                                   THEN snapshotStore[t][k] ELSE NoVal]]
    /\ pc' = [pc EXCEPT ![t] = "UPDATE"]
    /\ UNCHANGED << store, tx, missed, snapshotStore, read_keys, write_keys,
                    committed >>

\* Write phase: apply the writes to the local snapshot.
Update(t) ==
    /\ pc[t] = "UPDATE"
    /\ snapshotStore' = [snapshotStore EXCEPT ![t] =
                            [k \in Key |-> IF k \in write_keys[t]
                                           THEN t ELSE snapshotStore[t][k]]]
    /\ pc' = [pc EXCEPT ![t] = "COMMIT"]
    /\ UNCHANGED << store, tx, missed, read_keys, write_keys, reads, committed >>

\* Commit with first-committer-wins conflict detection.
Commit(t) ==
    /\ pc[t] = "COMMIT"
    /\ tx' = tx \ {t}
    /\ pc' = [pc EXCEPT ![t] = "Done"]
    /\ IF missed[t] \cap write_keys[t] = {}
       THEN /\ missed' = [o \in TxId |-> IF o \in tx'
                                         THEN missed[o] \cup write_keys[t]
                                         ELSE missed[o]]
            /\ store' = [k \in Key |-> IF k \in write_keys[t]
                                       THEN snapshotStore[t][k] ELSE store[k]]
            /\ committed' = committed \cup {t}
       ELSE \* conflict: abort, writes are discarded
            UNCHANGED << missed, store, committed >>
    /\ UNCHANGED << snapshotStore, read_keys, write_keys, reads >>

Proc(t) == Start(t) \/ Read(t) \/ Update(t) \/ Commit(t)

\* Allow stuttering only once every transaction has finished.
Terminating == /\ \A t \in TxId : pc[t] = "Done"
               /\ UNCHANGED vars

Next == (\E t \in TxId : Proc(t)) \/ Terminating

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A t \in TxId : WF_vars(Proc(t))

Termination == <>(\A t \in TxId : pc[t] = "Done")

-----------------------------------------------------------------------------
TypeOK ==
    /\ store \in [Key -> Val]
    /\ tx \subseteq TxId
    /\ missed \in [TxId -> SUBSET Key]
    /\ pc \in [TxId -> {"START", "READ", "UPDATE", "COMMIT", "Done"}]
    /\ snapshotStore \in [TxId -> [Key -> Val]]
    /\ read_keys \in [TxId -> SUBSET Key]
    /\ write_keys \in [TxId -> SUBSET Key]
    /\ reads \in [TxId -> [Key -> Val]]
    /\ committed \subseteq TxId

-----------------------------------------------------------------------------
(***************************************************************************)
(* Client-centric isolation checking.                                      *)
(* An execution is a total order (permutation) of committed transactions.  *)
(* StateAt(e, j) is the store after applying the first j transactions of   *)
(* e to the initial store.                                                 *)
(***************************************************************************)
Orders(S) ==
    { e \in [1..Cardinality(S) -> S] :
        \A i, j \in 1..Cardinality(S) : i # j => e[i] # e[j] }

RECURSIVE StateAt(_, _)
StateAt(e, j) ==
    IF j = 0 THEN InitStore
    ELSE LET prev == StateAt(e, j - 1)
         IN  [k \in Key |-> IF k \in write_keys[e[j]] THEN e[j] ELSE prev[k]]

\* All reads of transaction t are consistent with state s.
ReadsFrom(t, s) == \A k \in read_keys[t] : reads[t][k] = s[k]

\* Commit test for snapshot isolation at position i of execution e.
\* The test needs a read state j at or before the parent state (i - 1).
\* No transaction committed after state j and before i may write a key
\* that e[i] also writes.
CT_SI(e, i) ==
    \E j \in 0..(i - 1) :
        /\ ReadsFrom(e[i], StateAt(e, j))
        /\ \A l \in (j + 1)..(i - 1) :
              write_keys[e[l]] \cap write_keys[e[i]] = {}

\* Commit test for serializability: all reads come from the parent state.
CT_SER(e, i) == ReadsFrom(e[i], StateAt(e, i - 1))

SnapshotIsolation ==
    \E e \in Orders(committed) :
        \A i \in 1..Cardinality(committed) : CT_SI(e, i)

Serialization ==
    \E e \in Orders(committed) :
        \A i \in 1..Cardinality(committed) : CT_SER(e, i)

=============================================================================