---------------------------- MODULE MCKVsnap ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* Model values for the finite instantiation
CONSTANTS k1, k2, t1, t2, t3, NoVal

Key  == {k1, k2}
TxId == {t1, t2, t3}

\* Symmetry set over transaction identifiers
TxIdSymmetric == Permutations(TxId)

VARIABLES
    store,          \* the shared key-value store
    tx,             \* set of currently active transactions
    missed,         \* per tx: keys written by txs that committed while it was active
    pc,             \* program counter of each transaction
    snapshotStore,  \* per tx: private snapshot taken at start (plus local writes)
    read_keys,      \* per tx: keys it reads
    write_keys,     \* per tx: keys it writes
    readVals,       \* per tx: values observed during the read phase
    startTs,        \* per tx: logical start timestamp
    commitTs,       \* per tx: logical commit timestamp
    clock,          \* logical clock
    committed       \* set of successfully committed transactions

vars == << store, tx, missed, pc, snapshotStore, read_keys, write_keys,
           readVals, startTs, commitTs, clock, committed >>

Val == TxId \cup {NoVal}

-----------------------------------------------------------------------------
Init ==
    /\ store = [k \in Key |-> NoVal]
    /\ tx = {}
    /\ missed = [t \in TxId |-> {}]
    /\ pc = [t \in TxId |-> "START"]
    /\ snapshotStore = [t \in TxId |-> [k \in Key |-> NoVal]]
    /\ read_keys = [t \in TxId |-> {}]
    /\ write_keys = [t \in TxId |-> {}]
    /\ readVals = [t \in TxId |-> [k \in Key |-> NoVal]]
    /\ startTs = [t \in TxId |-> 0]
    /\ commitTs = [t \in TxId |-> 0]
    /\ clock = 0
    /\ committed = {}

\* Begin transaction: take a snapshot of the store, choose read/write sets
Start(self) ==
    /\ pc[self] = "START"
    /\ tx' = tx \cup {self}
    /\ snapshotStore' = [snapshotStore EXCEPT ![self] = store]
    /\ \E rk \in SUBSET Key \ {{}}, wk \in SUBSET Key \ {{}} :
          /\ read_keys' = [read_keys EXCEPT ![self] = rk]
          /\ write_keys' = [write_keys EXCEPT ![self] = wk]
    /\ clock' = clock + 1
    /\ startTs' = [startTs EXCEPT ![self] = clock + 1]
    /\ pc' = [pc EXCEPT ![self] = "READ"]
    /\ UNCHANGED << store, missed, readVals, commitTs, committed >>

\* Read from the snapshot
Read(self) ==
    /\ pc[self] = "READ"
    /\ readVals' = [readVals EXCEPT ![self] =
          [k \in Key |-> IF k \in read_keys[self]
                            THEN snapshotStore[self][k] ELSE NoVal]]
    /\ pc' = [pc EXCEPT ![self] = "UPDATE"]
    /\ UNCHANGED << store, tx, missed, snapshotStore, read_keys, write_keys,
                    startTs, commitTs, clock, committed >>

\* Perform writes locally in the snapshot
Update(self) ==
    /\ pc[self] = "UPDATE"
    /\ snapshotStore' = [snapshotStore EXCEPT ![self] =
          [k \in Key |-> IF k \in write_keys[self]
                            THEN self ELSE snapshotStore[self][k]]]
    /\ pc' = [pc EXCEPT ![self] = "COMMIT"]
    /\ UNCHANGED << store, tx, missed, read_keys, write_keys, readVals,
                    startTs, commitTs, clock, committed >>

\* Commit if no write-write conflict with concurrently committed txs, else abort
Commit(self) ==
    /\ pc[self] = "COMMIT"
    /\ LET txRest == tx \ {self} IN
       /\ tx' = txRest
       /\ IF missed[self] \cap write_keys[self] = {}
             THEN /\ missed' = [o \in TxId |->
                        IF o \in txRest THEN missed[o] \cup write_keys[self]
                                        ELSE missed[o]]
                  /\ store' = [k \in Key |->
                        IF k \in write_keys[self]
                           THEN snapshotStore[self][k] ELSE store[k]]
                  /\ committed' = committed \cup {self}
                  /\ clock' = clock + 1
                  /\ commitTs' = [commitTs EXCEPT ![self] = clock + 1]
             ELSE /\ UNCHANGED << missed, store, committed, clock, commitTs >>
    /\ pc' = [pc EXCEPT ![self] = "Done"]
    /\ UNCHANGED << snapshotStore, read_keys, write_keys, readVals, startTs >>

Proc(self) == Start(self) \/ Read(self) \/ Update(self) \/ Commit(self)

Terminating ==
    /\ \A t \in TxId : pc[t] = "Done"
    /\ UNCHANGED vars

Next == (\E t \in TxId : Proc(t)) \/ Terminating

Spec == Init /\ [][Next]_vars /\ \A t \in TxId : WF_vars(Proc(t))

-----------------------------------------------------------------------------
\* Safety properties

TypeOK ==
    /\ store \in [Key -> Val]
    /\ tx \subseteq TxId
    /\ missed \in [TxId -> SUBSET Key]
    /\ pc \in [TxId -> {"START", "READ", "UPDATE", "COMMIT", "Done"}]
    /\ snapshotStore \in [TxId -> [Key -> Val]]
    /\ read_keys \in [TxId -> SUBSET Key]
    /\ write_keys \in [TxId -> SUBSET Key]
    /\ readVals \in [TxId -> [Key -> Val]]
    /\ startTs \in [TxId -> Nat]
    /\ commitTs \in [TxId -> Nat]
    /\ clock \in Nat
    /\ committed \subseteq TxId

\* Value of key k visible to a snapshot taken at time ts
SnapshotValue(k, ts) ==
    LET W == {c \in committed : k \in write_keys[c] /\ commitTs[c] < ts}
    IN IF W = {} THEN NoVal
       ELSE CHOOSE c \in W : \A d \in W : commitTs[d] <= commitTs[c]

SnapshotIsolation ==
    \* Reads of committed txs come from the snapshot at their start time
    /\ \A t \in committed : \A k \in read_keys[t] :
          readVals[t][k] = SnapshotValue(k, startTs[t])
    \* No two concurrent committed txs write the same key (first committer wins)
    /\ \A a, b \in committed :
          ( /\ a # b
            /\ startTs[a] < commitTs[b]
            /\ startTs[b] < commitTs[a] )
          => write_keys[a] \cap write_keys[b] = {}

\* Serializability: some serial order of committed txs explains all reads
RECURSIVE SerialOK(_, _)
SerialOK(s, st) ==
    IF s = << >> THEN TRUE
    ELSE LET t == Head(s) IN
         /\ \A k \in read_keys[t] : readVals[t][k] = st[k]
         /\ SerialOK(Tail(s),
                     [k \in Key |-> IF k \in write_keys[t] THEN t ELSE st[k]])

Orders ==
    { f \in [1..Cardinality(committed) -> committed] :
        \A i, j \in 1..Cardinality(committed) : i # j => f[i] # f[j] }

Serialization ==
    \A t \in TxId : pc[t] = "Done" =>
        \E f \in Orders : SerialOK(f, [k \in Key |-> NoVal])

\* Debugging aid: violated when distinct keys hold distinct non-null values
\* after a certain search depth
BaitInv ==
    \/ TLCGet("level") < 14
    \/ ~ \E a, b \in Key :
          /\ a # b
          /\ store[a] # NoVal
          /\ store[b] # NoVal
          /\ store[a] # store[b]

-----------------------------------------------------------------------------
\* Liveness property

Termination == <>(\A t \in TxId : pc[t] = "Done")

=============================================================================