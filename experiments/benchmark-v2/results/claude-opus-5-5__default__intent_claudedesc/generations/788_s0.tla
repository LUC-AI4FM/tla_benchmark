---------------------------- MODULE KVSnapshotIsolation ----------------------------
(***************************************************************************)
(* Key-value store with snapshot isolation (first-committer-wins).         *)
(*                                                                         *)
(* Each transaction takes a snapshot of the store when it begins. It reads *)
(* from that private snapshot, applies its writes to the snapshot, and     *)
(* then tries to commit. The commit succeeds only if no key in its write   *)
(* set was written by a transaction that committed after the snapshot was  *)
(* taken. Those "missed" writes are tracked in `missed`.                    *)
(*                                                                         *)
(* Committed transactions are recorded as operation histories. These are   *)
(* the read/write records used by the client-centric model of isolation    *)
(* (Crooks et al.). The client-centric snapshot isolation condition is     *)
(* defined inline below, so the module is self-contained and parses with   *)
(* SANY on its own.                                                        *)
(*                                                                         *)
(* Serializability is NOT required: write skew is allowed.                 *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Key,        \* set of keys
    TxId,       \* set of transaction identifiers
    NoVal       \* "no value" marker for unwritten keys

ASSUME NoVal \notin TxId

VARIABLES
    store,          \* shared store: Key -> value
    tx,             \* set of currently active (begun, not finished) txns
    missed,         \* missed[t]: keys written by txns committed since t began
    snapshotStore,  \* snapshotStore[t]: t's private snapshot of the store
    readKeys,       \* readKeys[t]: keys t reads
    writeKeys,      \* writeKeys[t]: keys t writes
    ops,            \* ops[t]: history of t's operations (client-centric form)
    committed,      \* sequence of committed txns in commit order
    pc              \* program counter per transaction

vars == << store, tx, missed, snapshotStore, readKeys, writeKeys,
           ops, committed, pc >>

Value == TxId \cup {NoVal}

(***************************************************************************)
(* Client-centric operation records                                       *)
(***************************************************************************)
r(k, v) == [op |-> "read",  key |-> k, value |-> v]
w(k, v) == [op |-> "write", key |-> k, value |-> v]

Operation == [op : {"read", "write"}, key : Key, value : Value]

InitState == [k \in Key |-> NoVal]

\* Deterministically lists the elements of a finite set as a sequence.
SetToSeq(S) ==
    CHOOSE f \in [1..Cardinality(S) -> S] :
        \A i, j \in 1..Cardinality(S) : i # j => f[i] # f[j]

Range(f) == { f[x] : x \in DOMAIN f }

(***************************************************************************)
(* Initial state                                                           *)
(***************************************************************************)
Init ==
    /\ store = [k \in Key |-> NoVal]
    /\ tx = {}
    /\ missed = [t \in TxId |-> {}]
    /\ snapshotStore = [t \in TxId |-> [k \in Key |-> NoVal]]
    /\ readKeys = [t \in TxId |-> {}]
    /\ writeKeys = [t \in TxId |-> {}]
    /\ ops = [t \in TxId |-> << >>]
    /\ committed = << >>
    /\ pc = [t \in TxId |-> "START"]

(***************************************************************************)
(* Transaction actions                                                     *)
(***************************************************************************)

\* Begin: take a consistent snapshot and choose the read and write sets.
Start(t) ==
    /\ pc[t] = "START"
    /\ snapshotStore' = [snapshotStore EXCEPT ![t] = store]
    /\ tx' = tx \cup {t}
    /\ missed' = [missed EXCEPT ![t] = {}]
    /\ \E rk \in SUBSET Key, wk \in SUBSET Key :
          /\ readKeys'  = [readKeys  EXCEPT ![t] = rk]
          /\ writeKeys' = [writeKeys EXCEPT ![t] = wk]
    /\ pc' = [pc EXCEPT ![t] = "READ"]
    /\ UNCHANGED << store, ops, committed >>

\* Read phase: read the chosen keys from the private snapshot.
Read(t) ==
    /\ pc[t] = "READ"
    /\ LET rs == SetToSeq(readKeys[t])
       IN ops' = [ops EXCEPT ![t] =
                    [i \in 1..Len(rs) |-> r(rs[i], snapshotStore[t][rs[i]])]]
    /\ pc' = [pc EXCEPT ![t] = "UPDATE"]
    /\ UNCHANGED << store, tx, missed, snapshotStore, readKeys,
                    writeKeys, committed >>

\* Write phase: write own id into the local snapshot for each write key.
Update(t) ==
    /\ pc[t] = "UPDATE"
    /\ snapshotStore' = [snapshotStore EXCEPT ![t] =
                           [k \in Key |-> IF k \in writeKeys[t] THEN t
                                          ELSE snapshotStore[t][k]]]
    /\ pc' = [pc EXCEPT ![t] = "COMMIT"]
    /\ UNCHANGED << store, tx, missed, readKeys, writeKeys, ops, committed >>

\* Commit: first committer wins.
Commit(t) ==
    /\ pc[t] = "COMMIT"
    /\ tx' = tx \ {t}
    /\ pc' = [pc EXCEPT ![t] = "Done"]
    /\ IF missed[t] \cap writeKeys[t] = {}
         THEN \* no write-write conflict: install writes
              /\ store' = [k \in Key |-> IF k \in writeKeys[t] THEN t
                                         ELSE store[k]]
              /\ missed' = [o \in TxId |->
                              IF o \in tx \ {t}
                                THEN missed[o] \cup writeKeys[t]
                                ELSE missed[o]]
              /\ LET ws == SetToSeq(writeKeys[t])
                 IN ops' = [ops EXCEPT ![t] =
                              ops[t] \o [i \in 1..Len(ws) |-> w(ws[i], t)]]
              /\ committed' = Append(committed, t)
         ELSE \* conflict: abort, discard writes
              /\ UNCHANGED << store, missed, ops, committed >>
    /\ UNCHANGED << snapshotStore, readKeys, writeKeys >>

Proc(t) == Start(t) \/ Read(t) \/ Update(t) \/ Commit(t)

\* Stuttering once every transaction is done, so termination is not reported as deadlock.
Terminating ==
    /\ \A t \in TxId : pc[t] = "Done"
    /\ UNCHANGED vars

Next == (\E t \in TxId : Proc(t)) \/ Terminating

Spec == Init /\ [][Next]_vars /\ \A t \in TxId : WF_vars(Proc(t))

(***************************************************************************)
(* Type safety                                                             *)
(***************************************************************************)
TypeOK ==
    /\ store \in [Key -> Value]
    /\ tx \subseteq TxId
    /\ missed \in [TxId -> SUBSET Key]
    /\ snapshotStore \in [TxId -> [Key -> Value]]
    /\ readKeys \in [TxId -> SUBSET Key]
    /\ writeKeys \in [TxId -> SUBSET Key]
    /\ ops \in [TxId -> Seq(Operation)]
    /\ committed \in Seq(TxId)
    /\ pc \in [TxId -> {"START", "READ", "UPDATE", "COMMIT", "Done"}]

(***************************************************************************)
(* Client-centric snapshot isolation (Crooks et al.)                       *)
(*                                                                         *)
(* An execution is an ordering of committed transactions. State 0 is the   *)
(* initial state. State i is the result of applying the first i            *)
(* transactions. Transaction T at position i satisfies CT_SI if there is   *)
(* a state s_j with j < i such that:                                       *)
(*   - COMPLETE: every read in T returns s_j's value, or the value of T's  *)
(*     own preceding write to that key.                                    *)
(*   - NO-CONF: no transaction between positions j+1 and i-1 writes a key  *)
(*     that T also writes.                                                 *)
(***************************************************************************)
WK(t) == { ops[t][i].key : i \in { j \in DOMAIN ops[t] : ops[t][j].op = "write" } }

ApplyTx(s, t) ==
    [k \in Key |->
        IF k \in WK(t)
          THEN (CHOOSE i \in DOMAIN ops[t] :
                    /\ ops[t][i].op = "write" /\ ops[t][i].key = k
                    /\ \A j \in DOMAIN ops[t] :
                          (ops[t][j].op = "write" /\ ops[t][j].key = k) => j <= i
               ).value
          ELSE s[k]]

RECURSIVE StateAt(_, _)
StateAt(ord, i) ==
    IF i = 0 THEN InitState ELSE ApplyTx(StateAt(ord, i - 1), ord[i])

\* COMPLETE: reads match state s or the txn's latest earlier write.
ReadsOK(t, s) ==
    \A i \in DOMAIN ops[t] :
        ops[t][i].op = "read" =>
            LET k     == ops[t][i].key
                prior == { j \in 1..(i - 1) :
                              ops[t][j].op = "write" /\ ops[t][j].key = k }
            IN IF prior = {}
                 THEN ops[t][i].value = s[k]
                 ELSE \E j \in prior :
                         /\ \A j2 \in prior : j2 <= j
                         /\ ops[t][i].value = ops[t][j].value

Orders(C) ==
    { f \in [1..Cardinality(C) -> C] :
        \A i, j \in 1..Cardinality(C) : i # j => f[i] # f[j] }

CT_SI(ord, i) ==
    \E j \in 0..(i - 1) :
        /\ ReadsOK(ord[i], StateAt(ord, j))
        /\ \A m \in (j + 1)..(i - 1) : WK(ord[m]) \cap WK(ord[i]) = {}

SatisfyIsolationLevel(C) ==
    \E ord \in Orders(C) : \A i \in 1..Len(ord) : CT_SI(ord, i)

\* Main safety property: the observed history of committed transactions satisfies SI.
SnapshotIsolation == SatisfyIsolationLevel(Range(committed))

\* The commit order itself witnesses SI (stronger and cheaper to check).
SnapshotIsolationCommitOrder == \A i \in 1..Len(committed) : CT_SI(committed, i)

(***************************************************************************)
(* Deadlock freedom and liveness                                           *)
(***************************************************************************)
DeadlockFreedom ==
    (\E t \in TxId : pc[t] # "Done") => \E t \in TxId : ENABLED Proc(t)

\* Every transaction eventually completes, by commit or abort.
Termination == <>(\A t \in TxId : pc[t] = "Done")

TxTermination == \A t \in TxId : (pc[t] = "START") ~> (pc[t] = "Done")

THEOREM Spec => [](TypeOK /\ SnapshotIsolation /\ DeadlockFreedom)
THEOREM Spec => Termination
=============================================================================