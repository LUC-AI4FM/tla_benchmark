------------------------------- MODULE MC -------------------------------
(***************************************************************************)
(* Model-checking wrapper for a key-value store with snapshot isolation    *)
(* (KVsnap). The underlying KVsnap behavior is inlined so the module is    *)
(* self-contained. On top of it, the module defines TLC helpers: a         *)
(* symmetry set over transaction identifiers and a level-gated debugging   *)
(* invariant.                                                              *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Key, TxId, NoVal

ASSUME NoVal \notin TxId

VARIABLES store, tx, missed, pc, snapshotStore, read_keys, write_keys,
          clock, startTs, commitTs, committed

vars == << store, tx, missed, pc, snapshotStore, read_keys, write_keys,
           clock, startTs, commitTs, committed >>

Val == TxId \cup {NoVal}

TypeOK ==
    /\ store \in [Key -> Val]
    /\ tx \subseteq TxId
    /\ missed \in [TxId -> SUBSET Key]
    /\ pc \in [TxId -> {"START", "UPDATE", "COMMIT", "Done"}]
    /\ snapshotStore \in [TxId -> [Key -> Val]]
    /\ read_keys \in [TxId -> SUBSET Key]
    /\ write_keys \in [TxId -> SUBSET Key]
    /\ clock \in Nat
    /\ startTs \in [TxId -> Nat]
    /\ commitTs \in [TxId -> Nat]
    /\ committed \subseteq TxId

Init ==
    /\ store = [k \in Key |-> NoVal]
    /\ tx = {}
    /\ missed = [t \in TxId |-> {}]
    /\ pc = [t \in TxId |-> "START"]
    /\ snapshotStore = [t \in TxId |-> [k \in Key |-> NoVal]]
    /\ read_keys = [t \in TxId |-> {}]
    /\ write_keys = [t \in TxId |-> {}]
    /\ clock = 0
    /\ startTs = [t \in TxId |-> 0]
    /\ commitTs = [t \in TxId |-> 0]
    /\ committed = {}

(* A transaction begins: takes a snapshot and chooses its read/write sets *)
Start(self) ==
    /\ pc[self] = "START"
    /\ tx' = tx \cup {self}
    /\ snapshotStore' = [snapshotStore EXCEPT ![self] = store]
    /\ \E rk \in SUBSET Key, wk \in SUBSET Key :
          /\ read_keys' = [read_keys EXCEPT ![self] = rk]
          /\ write_keys' = [write_keys EXCEPT ![self] = wk]
    /\ clock' = clock + 1
    /\ startTs' = [startTs EXCEPT ![self] = clock + 1]
    /\ pc' = [pc EXCEPT ![self] = "UPDATE"]
    /\ UNCHANGED << store, missed, commitTs, committed >>

(* Local updates are applied to the transaction's private snapshot *)
Update(self) ==
    /\ pc[self] = "UPDATE"
    /\ snapshotStore' = [snapshotStore EXCEPT ![self] =
          [k \in Key |-> IF k \in write_keys[self]
                            THEN self
                            ELSE snapshotStore[self][k]]]
    /\ pc' = [pc EXCEPT ![self] = "COMMIT"]
    /\ UNCHANGED << store, tx, missed, read_keys, write_keys,
                    clock, startTs, commitTs, committed >>

(* Commit if no write-write conflict with concurrently committed txns,   *)
(* otherwise abort.                                                        *)
Commit(self) ==
    /\ pc[self] = "COMMIT"
    /\ tx' = tx \ {self}
    /\ pc' = [pc EXCEPT ![self] = "Done"]
    /\ IF missed[self] \cap write_keys[self] = {}
         THEN /\ store' = [k \in Key |-> IF k \in write_keys[self]
                                            THEN snapshotStore[self][k]
                                            ELSE store[k]]
              /\ missed' = [o \in TxId |->
                              IF o \in tx \ {self}
                                 THEN missed[o] \cup write_keys[self]
                                 ELSE missed[o]]
              /\ clock' = clock + 1
              /\ commitTs' = [commitTs EXCEPT ![self] = clock + 1]
              /\ committed' = committed \cup {self}
         ELSE UNCHANGED << store, missed, clock, commitTs, committed >>
    /\ UNCHANGED << snapshotStore, read_keys, write_keys, startTs >>

t(self) == Start(self) \/ Update(self) \/ Commit(self)

Terminating ==
    /\ \A self \in TxId : pc[self] = "Done"
    /\ UNCHANGED vars

Next == (\E self \in TxId : t(self)) \/ Terminating

Spec == Init /\ [][Next]_vars /\ \A self \in TxId : WF_vars(t(self))

(* Committed transactions that are concurrent never write the same key,  *)
(* and every transaction reads from a consistent snapshot.                *)
SnapshotIsolation ==
    \A t1, t2 \in committed :
        (t1 # t2 /\ write_keys[t1] \cap write_keys[t2] # {})
           => \/ commitTs[t1] < startTs[t2]
              \/ commitTs[t2] < startTs[t1]

Termination == <>(\A self \in TxId : pc[self] = "Done")

----------------------------------------------------------------------------
(* TLC-specific helpers *)

TxIdSymmetric == Permutations(TxId)

DebugLevel == 5

DebugInv ==
    TLCGet("level") > DebugLevel =>
        \A k1, k2 \in Key :
            ~( /\ k1 # k2
               /\ store[k1] # NoVal
               /\ store[k2] # NoVal
               /\ store[k1] # store[k2] )
=============================================================================