---------------------------- MODULE KVsnap ----------------------------
(***************************************************************************)
(* A key-value store with snapshot isolation.  Each transaction:           *)
(*   START  : joins the active set, takes an atomic snapshot of the store  *)
(*            and nondeterministically picks its read and write key sets.  *)
(*   READ   : reads its keys from the snapshot and logs the reads.         *)
(*   UPDATE : writes its keys into its local snapshot and logs the writes. *)
(*   COMMIT : if no key it writes was written by a transaction that        *)
(*            committed after its snapshot (the "missed" keys), it applies *)
(*            its writes atomically to the store and adds its write keys   *)
(*            to the missed sets of all other active transactions.         *)
(*            Otherwise it aborts and its operation log is discarded.      *)
(* The operation log is checked against client-centric definitions of     *)
(* Serializability and Snapshot Isolation (in the style of Crooks et al.). *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Key, TxId, NoVal

ASSUME NoVal \notin TxId

VARIABLES store, tx, missed, snapshotStore, read_keys, write_keys, ops, pc

vars == <<store, tx, missed, snapshotStore, read_keys, write_keys, ops, pc>>

ProcSet == TxId

Values == TxId \cup {NoVal}

InitialState == [k \in Key |-> NoVal]

(***************************************************************************)
(* Operations of the abstract log                                          *)
(***************************************************************************)
Operation == [op : {"read", "write"}, key : Key, value : Values]

rOp(k, v) == [op |-> "read",  key |-> k, value |-> v]
wOp(k, v) == [op |-> "write", key |-> k, value |-> v]

SetToSeq(S) ==
    CHOOSE f \in [1..Cardinality(S) -> S] :
        \A i, j \in 1..Cardinality(S) : i # j => f[i] # f[j]

(***************************************************************************)
(* Type invariant                                                          *)
(***************************************************************************)
TypeOK ==
    /\ store \in [Key -> Values]
    /\ tx \subseteq TxId
    /\ missed \in [TxId -> SUBSET Key]
    /\ snapshotStore \in [TxId -> [Key -> Values]]
    /\ read_keys \in [TxId -> SUBSET Key]
    /\ write_keys \in [TxId -> SUBSET Key]
    /\ ops \in [TxId -> Seq(Operation)]
    /\ pc \in [TxId -> {"START", "READ", "UPDATE", "COMMIT", "Done"}]

(***************************************************************************)
(* Initial state                                                           *)
(***************************************************************************)
Init ==
    /\ store = [k \in Key |-> NoVal]
    /\ tx = {}
    /\ missed = [t \in TxId |-> {}]
    /\ snapshotStore = [t \in TxId |-> [k \in Key |-> NoVal]]
    /\ read_keys = [t \in TxId |-> {}]
    /\ write_keys = [t \in TxId |-> {}]
    /\ ops = [t \in TxId |-> <<>>]
    /\ pc = [t \in TxId |-> "START"]

(***************************************************************************)
(* Transaction steps                                                       *)
(***************************************************************************)
Start(self) ==
    /\ pc[self] = "START"
    /\ tx' = tx \cup {self}
    /\ snapshotStore' = [snapshotStore EXCEPT ![self] = store]
    /\ \E rk \in SUBSET Key \ {{}}, wk \in SUBSET Key \ {{}} :
          /\ read_keys' = [read_keys EXCEPT ![self] = rk]
          /\ write_keys' = [write_keys EXCEPT ![self] = wk]
    /\ pc' = [pc EXCEPT ![self] = "READ"]
    /\ UNCHANGED <<store, missed, ops>>

Read(self) ==
    /\ pc[self] = "READ"
    /\ ops' = [ops EXCEPT ![self] =
                 @ \o SetToSeq({rOp(k, snapshotStore[self][k]) : k \in read_keys[self]})]
    /\ pc' = [pc EXCEPT ![self] = "UPDATE"]
    /\ UNCHANGED <<store, tx, missed, snapshotStore, read_keys, write_keys>>

Update(self) ==
    /\ pc[self] = "UPDATE"
    /\ snapshotStore' = [snapshotStore EXCEPT ![self] =
                           [k \in Key |-> IF k \in write_keys[self]
                                            THEN self
                                            ELSE snapshotStore[self][k]]]
    /\ ops' = [ops EXCEPT ![self] =
                 @ \o SetToSeq({wOp(k, self) : k \in write_keys[self]})]
    /\ pc' = [pc EXCEPT ![self] = "COMMIT"]
    /\ UNCHANGED <<store, tx, missed, read_keys, write_keys>>

Commit(self) ==
    /\ pc[self] = "COMMIT"
    /\ IF missed[self] \cap write_keys[self] = {}
         THEN /\ tx' = tx \ {self}
              /\ missed' = [o \in TxId |->
                              IF o \in tx' THEN missed[o] \cup write_keys[self]
                                           ELSE missed[o]]
              /\ store' = [k \in Key |-> IF k \in write_keys[self]
                                           THEN snapshotStore[self][k]
                                           ELSE store[k]]
              /\ UNCHANGED ops
         ELSE \* conflict detected: abort, nothing applied, log discarded
              /\ tx' = tx \ {self}
              /\ ops' = [ops EXCEPT ![self] = <<>>]
              /\ UNCHANGED <<store, missed>>
    /\ pc' = [pc EXCEPT ![self] = "Done"]
    /\ UNCHANGED <<snapshotStore, read_keys, write_keys>>

Proc(self) == Start(self) \/ Read(self) \/ Update(self) \/ Commit(self)

Terminating == /\ \A self \in ProcSet : pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in TxId : Proc(self)) \/ Terminating

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in TxId : WF_vars(Proc(self))

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

(***************************************************************************)
(* Client-centric consistency checking over the operation log             *)
(***************************************************************************)
CommittedTxns == {ops[t] : t \in {u \in TxId : pc[u] = "Done" /\ ops[u] # <<>>}}

WriteKeysOf(T) == {T[i].key : i \in {j \in DOMAIN T : T[j].op = "write"}}

Effects(s, T) ==
    [k \in Key |->
        LET idx == {i \in DOMAIN T : T[i].op = "write" /\ T[i].key = k}
        IN IF idx = {} THEN s[k]
           ELSE T[CHOOSE m \in idx : \A n \in idx : n <= m].value]

Orderings(S) ==
    {f \in [1..Cardinality(S) -> S] :
        \A i, j \in 1..Cardinality(S) : i # j => f[i] # f[j]}

ExecStates(ord) ==
    LET n == Cardinality(DOMAIN ord)
        st[i \in 0..n] == IF i = 0 THEN InitialState
                                   ELSE Effects(st[i-1], ord[i])
    IN st

\* Every read of T is explained by state s (or by an earlier own write).
Complete(T, s) ==
    \A p \in DOMAIN T :
        T[p].op = "read" =>
            \/ s[T[p].key] = T[p].value
            \/ \E q \in 1..(p-1) : /\ T[q].op = "write"
                                   /\ T[q].key = T[p].key
                                   /\ T[q].value = T[p].value

SerializabilityOf(Txns) ==
    \E ord \in Orderings(Txns) :
        LET st == ExecStates(ord)
        IN \A i \in DOMAIN ord : Complete(ord[i], st[i-1])

SnapshotIsolationOf(Txns) ==
    \E ord \in Orderings(Txns) :
        LET st == ExecStates(ord)
        IN \A i \in DOMAIN ord :
              \E j \in 0..(i-1) :
                  /\ Complete(ord[i], st[j])
                  /\ \A k \in WriteKeysOf(ord[i]) : st[j][k] = st[i-1][k]

\* Expected to be violated (write skew is allowed under SI).
Serialization == SerializabilityOf(CommittedTxns)

SnapshotIsolation == SnapshotIsolationOf(CommittedTxns)

(***************************************************************************)
(* Additional safety properties                                            *)
(***************************************************************************)
\* The store only ever holds values written by committed transactions.
StoreFromCommitted ==
    \A k \in Key : store[k] # NoVal =>
        /\ pc[store[k]] = "Done"
        /\ ops[store[k]] # <<>>
        /\ k \in write_keys[store[k]]

\* No committed transaction overwrote a key it had missed.
ConflictSafety ==
    \A t \in TxId : (pc[t] = "Done" /\ ops[t] # <<>>) =>
        missed[t] \cap write_keys[t] = {}

\* Active transactions are exactly those started but not finished.
TxLifecycle ==
    \A t \in TxId : (t \in tx) <=> pc[t] \in {"READ", "UPDATE", "COMMIT"}

=============================================================================