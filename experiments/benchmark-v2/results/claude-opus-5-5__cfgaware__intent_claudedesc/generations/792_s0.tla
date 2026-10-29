------------------------------ MODULE KVSnapshotIsolation ------------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Key,      \* set of keys
          TxId,     \* set of transaction identifiers
          NoVal     \* value of an empty / unset key

\* A transaction writes its own identifier as the value of every key it writes.
\* This lets different keys hold different values and makes values traceable.
Val == TxId

ASSUME NoVal \notin TxId

Store == [Key -> Val \cup {NoVal}]

VARIABLES
    store,      \* committed state of the key-value store
    tx,         \* set of currently open transactions
    pc,         \* lifecycle stage of each transaction
    snap,       \* private snapshot (plus own writes) of each transaction
    readKeys,   \* keys a transaction intends to read
    writeKeys,  \* keys a transaction intends to write
    readDone,   \* keys already read by a transaction
    written,    \* keys already written by a transaction
    observed,   \* set of <<key, value>> pairs read by a transaction
    missed,     \* keys written by transactions that committed while tx was open
    startTs,    \* index into log of the snapshot taken at transaction start
    log,        \* sequence of committed store versions
    history     \* set of committed transaction records

vars == << store, tx, pc, snap, readKeys, writeKeys, readDone, written,
           observed, missed, startTs, log, history >>

EmptyStore == [k \in Key |-> NoVal]

HistRec == [id : TxId, start : Nat, commit : Nat,
            reads : SUBSET (Key \X (Val \cup {NoVal})), writes : SUBSET Key]

TypeOK ==
    /\ store \in Store
    /\ tx \subseteq TxId
    /\ pc \in [TxId -> {"init", "active", "done"}]
    /\ snap \in [TxId -> Store]
    /\ readKeys \in [TxId -> SUBSET Key]
    /\ writeKeys \in [TxId -> SUBSET Key]
    /\ readDone \in [TxId -> SUBSET Key]
    /\ written \in [TxId -> SUBSET Key]
    /\ observed \in [TxId -> SUBSET (Key \X (Val \cup {NoVal}))]
    /\ missed \in [TxId -> SUBSET Key]
    /\ startTs \in [TxId -> Nat]
    /\ log \in Seq(Store)
    /\ history \subseteq HistRec

Init ==
    /\ store = EmptyStore
    /\ tx = {}
    /\ pc = [t \in TxId |-> "init"]
    /\ snap = [t \in TxId |-> EmptyStore]
    /\ readKeys = [t \in TxId |-> {}]
    /\ writeKeys = [t \in TxId |-> {}]
    /\ readDone = [t \in TxId |-> {}]
    /\ written = [t \in TxId |-> {}]
    /\ observed = [t \in TxId |-> {}]
    /\ missed = [t \in TxId |-> {}]
    /\ startTs = [t \in TxId |-> 0]
    /\ log = << EmptyStore >>
    /\ history = {}

\* Open a transaction: take a snapshot of the committed store.
Start(t) ==
    /\ pc[t] = "init"
    /\ \E rk \in SUBSET Key, wk \in SUBSET Key :
          /\ readKeys' = [readKeys EXCEPT ![t] = rk]
          /\ writeKeys' = [writeKeys EXCEPT ![t] = wk]
    /\ tx' = tx \cup {t}
    /\ pc' = [pc EXCEPT ![t] = "active"]
    /\ snap' = [snap EXCEPT ![t] = store]
    /\ startTs' = [startTs EXCEPT ![t] = Len(log)]
    /\ missed' = [missed EXCEPT ![t] = {}]
    /\ UNCHANGED << store, readDone, written, observed, log, history >>

\* Read a key from the transaction's snapshot.
Read(t, k) ==
    /\ pc[t] = "active"
    /\ k \in readKeys[t] \ readDone[t]
    /\ readDone' = [readDone EXCEPT ![t] = @ \cup {k}]
    /\ observed' = [observed EXCEPT ![t] = @ \cup {<< k, snap[t][k] >>}]
    /\ UNCHANGED << store, tx, pc, snap, readKeys, writeKeys, written,
                    missed, startTs, log, history >>

\* Write a key in the transaction's private snapshot.
Write(t, k) ==
    /\ pc[t] = "active"
    /\ k \in writeKeys[t] \ written[t]
    /\ snap' = [snap EXCEPT ![t][k] = t]
    /\ written' = [written EXCEPT ![t] = @ \cup {k}]
    /\ UNCHANGED << store, tx, pc, readKeys, writeKeys, readDone, observed,
                    missed, startTs, log, history >>

OpsDone(t) ==
    /\ readDone[t] = readKeys[t]
    /\ written[t] = writeKeys[t]

\* Commit, if no concurrent committed transaction wrote an overlapping key
\* (first-committer-wins).
Commit(t) ==
    /\ pc[t] = "active"
    /\ OpsDone(t)
    /\ missed[t] \cap written[t] = {}
    /\ LET newStore == [k \in Key |->
                          IF k \in written[t] THEN snap[t][k] ELSE store[k]]
       IN /\ store' = newStore
          /\ log' = Append(log, newStore)
          /\ history' = history \cup
                {[id |-> t, start |-> startTs[t], commit |-> Len(log) + 1,
                  reads |-> observed[t], writes |-> written[t]]}
    /\ tx' = tx \ {t}
    /\ pc' = [pc EXCEPT ![t] = "done"]
    /\ missed' = [o \in TxId |->
                    IF o \in tx /\ o # t THEN missed[o] \cup written[t]
                    ELSE missed[o]]
    /\ UNCHANGED << snap, readKeys, writeKeys, readDone, written, observed, startTs >>

\* Abort due to a write-write conflict with a concurrently committed transaction.
Abort(t) ==
    /\ pc[t] = "active"
    /\ OpsDone(t)
    /\ missed[t] \cap written[t] # {}
    /\ tx' = tx \ {t}
    /\ pc' = [pc EXCEPT ![t] = "done"]
    /\ UNCHANGED << store, snap, readKeys, writeKeys, readDone, written,
                    observed, missed, startTs, log, history >>

Proc(t) ==
    \/ Start(t)
    \/ \E k \in Key : Read(t, k) \/ Write(t, k)
    \/ Commit(t)
    \/ Abort(t)

Terminated ==
    /\ \A t \in TxId : pc[t] = "done"
    /\ UNCHANGED vars

Next == (\E t \in TxId : Proc(t)) \/ Terminated

Spec == Init /\ [][Next]_vars /\ \A t \in TxId : WF_vars(Proc(t))

----------------------------------------------------------------------------------------
\* Correctness properties

\* Every committed transaction read values from the single consistent snapshot
\* that existed when it started (or its own writes), and no two concurrent
\* committed transactions wrote a common key. The store is the latest version.
SnapshotIsolation ==
    /\ store = log[Len(log)]
    /\ \A h \in history :
          /\ h.start \in 1..Len(log)
          /\ h.commit \in 1..Len(log)
          /\ h.start < h.commit
          /\ \A r \in h.reads :
                \/ r[2] = log[h.start][r[1]]
                \/ (r[1] \in h.writes /\ r[2] = h.id)
          /\ \A k \in h.writes : log[h.commit][k] = h.id
    /\ \A h1, h2 \in history :
          (h1.id # h2.id /\ h1.writes \cap h2.writes # {}) =>
              (h1.commit <= h2.start \/ h2.commit <= h1.start)
    /\ \A h1, h2 \in history : h1.id # h2.id => h1.commit # h2.commit

Termination == <>(\A t \in TxId : pc[t] = "done")

TxIdSymmetric == Permutations(TxId)

========================================================================================