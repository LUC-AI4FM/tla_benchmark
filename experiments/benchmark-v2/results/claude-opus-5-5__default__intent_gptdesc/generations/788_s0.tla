------------------------------ MODULE KVSnapshotIsolation ------------------------------
(***************************************************************************)
(* A concurrent key-value store whose client transactions run under       *)
(* snapshot isolation (SI).                                                *)
(*                                                                         *)
(*  - A transaction starts by taking an instantaneous snapshot of the     *)
(*    global store.                                                        *)
(*  - It then reads from and writes to its own local snapshot only.       *)
(*  - It ends with an atomic commit. The commit is applied only if none   *)
(*    of the keys it wrote were written by a transaction that committed   *)
(*    after its snapshot, i.e. the "missed" writes. Otherwise it aborts.  *)
(*  - A successful commit adds its written keys to the "missed" set of    *)
(*    every other transaction that is still active.                       *)
(*                                                                         *)
(* An abstract operation log (per-transaction ops plus a global committed *)
(* history) supports client-centric checks. These checks validate SI and  *)
(* state serializability, which is expected to fail because of write skew.*)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Key,        \* set of keys
    Val,        \* set of values clients may write
    TxId,       \* finite set of transaction identifiers
    NoVal,      \* sentinel value: "key holds no value"
    MaxOps      \* bound on read/write operations per transaction (finite model)

ASSUME NoVal \notin Val
ASSUME Key # {} /\ TxId # {} /\ IsFiniteSet(TxId)
ASSUME MaxOps \in Nat

VARIABLES
    store,          \* global key-value store
    tx,             \* set of currently active transactions
    snapshotStore,  \* per-transaction local snapshot (incl. local writes)
    readSet,        \* per-transaction set of keys read
    writeSet,       \* per-transaction set of keys written
    missed,         \* per-transaction keys written by others after its snapshot
    txStatus,       \* per-transaction lifecycle status
    txStart,        \* per-transaction: # of commits visible in its snapshot
    ops,            \* per-transaction operation log
    history         \* sequence of committed transactions (in commit order)

vars == <<store, tx, snapshotStore, readSet, writeSet, missed,
          txStatus, txStart, ops, history>>

-----------------------------------------------------------------------------
(* Domains *)

Value     == Val \cup {NoVal}
Store     == [Key -> Value]
InitStore == [k \in Key |-> NoVal]
Status    == {"init", "active", "committed", "aborted"}

Op == [op : {"read", "write"}, key : Key, value : Value]

CommitRec == [ id     : TxId,
               start  : Nat,
               wset   : SUBSET Key,
               wstore : Store,
               reads  : SUBSET (Key \X Value),
               missed : SUBSET Key ]

(* The ith op of t is a read of a key that t had not written before it. *)
IsExternalRead(t, i) ==
    /\ ops[t][i].op = "read"
    /\ ~ \E j \in 1..(i - 1) :
            /\ ops[t][j].op = "write"
            /\ ops[t][j].key = ops[t][i].key

ExtReads(t) ==
    { <<ops[t][i].key, ops[t][i].value>> :
        i \in { j \in 1..Len(ops[t]) : IsExternalRead(t, j) } }

(* Global store obtained by applying the first n committed transactions. *)
RECURSIVE StoreAfter(_)
StoreAfter(n) ==
    IF n = 0 THEN InitStore
    ELSE [k \in Key |->
            IF k \in history[n].wset THEN history[n].wstore[k]
                                     ELSE StoreAfter(n - 1)[k]]

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ store         = InitStore
    /\ tx            = {}
    /\ snapshotStore = [t \in TxId |-> InitStore]
    /\ readSet       = [t \in TxId |-> {}]
    /\ writeSet      = [t \in TxId |-> {}]
    /\ missed        = [t \in TxId |-> {}]
    /\ txStatus      = [t \in TxId |-> "init"]
    /\ txStart       = [t \in TxId |-> 0]
    /\ ops           = [t \in TxId |-> << >>]
    /\ history       = << >>

-----------------------------------------------------------------------------
(* Actions *)

(* Begin: take an instantaneous snapshot of the global store. *)
OpenTx(t) ==
    /\ txStatus[t] = "init"
    /\ tx'            = tx \cup {t}
    /\ snapshotStore' = [snapshotStore EXCEPT ![t] = store]
    /\ txStatus'      = [txStatus EXCEPT ![t] = "active"]
    /\ txStart'       = [txStart EXCEPT ![t] = Len(history)]
    /\ missed'        = [missed EXCEPT ![t] = {}]
    /\ readSet'       = [readSet EXCEPT ![t] = {}]
    /\ writeSet'      = [writeSet EXCEPT ![t] = {}]
    /\ UNCHANGED <<store, ops, history>>

(* Read a nondeterministically chosen key from the local snapshot. *)
Read(t, k) ==
    /\ t \in tx
    /\ Len(ops[t]) < MaxOps
    /\ readSet' = [readSet EXCEPT ![t] = @ \cup {k}]
    /\ ops' = [ops EXCEPT ![t] =
                 Append(@, [op |-> "read", key |-> k,
                            value |-> snapshotStore[t][k]])]
    /\ UNCHANGED <<store, tx, snapshotStore, writeSet, missed,
                   txStatus, txStart, history>>

(* Local write: updates only the transaction's own snapshot. *)
Update(t, k, v) ==
    /\ t \in tx
    /\ Len(ops[t]) < MaxOps
    /\ snapshotStore' = [snapshotStore EXCEPT ![t][k] = v]
    /\ writeSet'      = [writeSet EXCEPT ![t] = @ \cup {k}]
    /\ ops' = [ops EXCEPT ![t] =
                 Append(@, [op |-> "write", key |-> k, value |-> v])]
    /\ UNCHANGED <<store, tx, readSet, missed, txStatus, txStart, history>>

(* A commit conflicts if it would overwrite keys it missed. *)
Conflict(t) == missed[t] \cap writeSet[t] # {}

(* Atomic commit: apply all local writes at once and propagate the written *)
(* keys to the missed sets of the other active transactions.               *)
CommitTx(t) ==
    /\ t \in tx
    /\ ~ Conflict(t)
    /\ tx'       = tx \ {t}
    /\ store'    = [k \in Key |->
                      IF k \in writeSet[t] THEN snapshotStore[t][k]
                                           ELSE store[k]]
    /\ missed'   = [o \in TxId |->
                      IF o \in tx' THEN missed[o] \cup writeSet[t]
                                   ELSE missed[o]]
    /\ txStatus' = [txStatus EXCEPT ![t] = "committed"]
    /\ history'  = Append(history,
                     [ id     |-> t,
                       start  |-> txStart[t],
                       wset   |-> writeSet[t],
                       wstore |-> snapshotStore[t],
                       reads  |-> ExtReads(t),
                       missed |-> missed[t] ])
    /\ UNCHANGED <<snapshotStore, readSet, writeSet, txStart, ops>>

(* Commit fails to apply because of a detected conflict: abort. *)
AbortTx(t) ==
    /\ t \in tx
    /\ Conflict(t)
    /\ tx'       = tx \ {t}
    /\ txStatus' = [txStatus EXCEPT ![t] = "aborted"]
    /\ UNCHANGED <<store, snapshotStore, readSet, writeSet, missed,
                   txStart, ops, history>>

(* Attempting to commit always terminates the transaction. *)
Terminate(t) == CommitTx(t) \/ AbortTx(t)

(* All transactions done: allow stuttering (no spurious deadlock). *)
Done ==
    /\ \A t \in TxId : txStatus[t] \in {"committed", "aborted"}
    /\ UNCHANGED vars

Next ==
    \/ \E t \in TxId : OpenTx(t)
    \/ \E t \in TxId, k \in Key : Read(t, k)
    \/ \E t \in TxId, k \in Key, v \in Val : Update(t, k, v)
    \/ \E t \in TxId : Terminate(t)
    \/ Done

Fairness ==
    \A t \in TxId : /\ WF_vars(OpenTx(t))
                    /\ WF_vars(Terminate(t))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Type invariant *)

TypeOK ==
    /\ store \in Store
    /\ tx \subseteq TxId
    /\ snapshotStore \in [TxId -> Store]
    /\ readSet  \in [TxId -> SUBSET Key]
    /\ writeSet \in [TxId -> SUBSET Key]
    /\ missed   \in [TxId -> SUBSET Key]
    /\ txStatus \in [TxId -> Status]
    /\ txStart  \in [TxId -> Nat]
    /\ \A t \in TxId : /\ ops[t] \in Seq(Op)
                       /\ Len(ops[t]) <= MaxOps
    /\ DOMAIN ops = TxId
    /\ history \in Seq(CommitRec)
    /\ Len(history) <= Cardinality(TxId)

(* Active set is exactly the set of transactions in status "active". *)
ActiveConsistent == tx = { t \in TxId : txStatus[t] = "active" }

-----------------------------------------------------------------------------
(* Snapshot isolation properties *)

(* Committed writes become visible atomically: the global store is exactly *)
(* the result of applying whole committed transactions in commit order.    *)
AtomicVisibility == store = StoreAfter(Len(history))

(* Each active transaction's snapshot equals the consistent store state at *)
(* its start (except keys it wrote itself), so it sees no partial effects. *)
SnapshotConsistency ==
    \A t \in tx : \A k \in Key \ writeSet[t] :
        snapshotStore[t][k] = StoreAfter(txStart[t])[k]

(* Every external read in the log returns the value of the start snapshot. *)
ReadsFromSnapshot ==
    \A t \in TxId : \A i \in 1..Len(ops[t]) :
        IsExternalRead(t, i) =>
            ops[t][i].value = StoreAfter(txStart[t])[ops[t][i].key]

(* Reads of locally written keys return the latest local write. *)
ReadYourWrites ==
    \A t \in TxId : \A i \in 1..Len(ops[t]) :
        (ops[t][i].op = "read" /\ ~ IsExternalRead(t, i)) =>
            \E j \in 1..(i - 1) :
                /\ ops[t][j].op = "write"
                /\ ops[t][j].key = ops[t][i].key
                /\ ops[t][j].value = ops[t][i].value
                /\ \A m \in (j + 1)..(i - 1) :
                       ~ (ops[t][m].op = "write" /\ ops[t][m].key = ops[t][i].key)

(* The missed set is exactly the union of keys written by transactions     *)
(* that committed after the snapshot was taken.                            *)
MissedCorrect ==
    \A t \in tx :
        missed[t] = UNION { history[i].wset : i \in (txStart[t] + 1)..Len(history) }

-----------------------------------------------------------------------------
(* Conflict-detection safety *)

(* No committed transaction overwrote a key it missed. *)
NoCommitOverMissed ==
    /\ \A i \in 1..Len(history) : history[i].missed \cap history[i].wset = {}
    /\ \A t \in TxId : txStatus[t] = "committed" => ~ Conflict(t)

(* First-committer-wins, checked from the history alone: two concurrent    *)
(* committed transactions never write a common key.                        *)
FirstCommitterWins ==
    \A i, j \in 1..Len(history) :
        (i < j /\ i > history[j].start) =>
            history[i].wset \cap history[j].wset = {}

(* Aborts happen only on a real conflict, so non-conflicting transactions  *)
(* (for example ones with disjoint write sets) are never prevented.        *)
AbortOnlyOnConflict ==
    \A t \in TxId : txStatus[t] = "aborted" => Conflict(t)

(* No lost updates: each committed write remains in the store unless a     *)
(* later committed transaction overwrote that same key.                    *)
NoLostUpdates ==
    \A i \in 1..Len(history) : \A k \in history[i].wset :
        (\A j \in (i + 1)..Len(history) : k \notin history[j].wset) =>
            store[k] = history[i].wstore[k]

SIInvariants ==
    /\ TypeOK
    /\ ActiveConsistent
    /\ AtomicVisibility
    /\ SnapshotConsistency
    /\ ReadsFromSnapshot
    /\ ReadYourWrites
    /\ MissedCorrect
    /\ NoCommitOverMissed
    /\ FirstCommitterWins
    /\ AbortOnlyOnConflict
    /\ NoLostUpdates

-----------------------------------------------------------------------------
(* Client-centric serializability check over the operation log.            *)
(* This is EXPECTED TO FAIL under SI because of write skew.                *)

Perms(n) == { f \in [1..n -> 1..n] : \A i, j \in 1..n : i # j => f[i] # f[j] }

(* Store after serially executing history[p[1]], ..., history[p[m]]. *)
RECURSIVE SerialStore(_, _)
SerialStore(p, m) ==
    IF m = 0 THEN InitStore
    ELSE [k \in Key |->
            IF k \in history[p[m]].wset THEN history[p[m]].wstore[k]
                                        ELSE SerialStore(p, m - 1)[k]]

(* Some serial order of the committed transactions explains every read. *)
Serializable ==
    LET n == Len(history) IN
    \E p \in Perms(n) :
        \A m \in 1..n : \A rv \in history[p[m]].reads :
            SerialStore(p, m - 1)[rv[1]] = rv[2]

-----------------------------------------------------------------------------
(* Liveness *)

EveryTxStarts == \A t \in TxId : <>(txStatus[t] # "init")

EveryTxTerminates ==
    \A t \in TxId : <>(txStatus[t] \in {"committed", "aborted"})

(* A transaction that is active and has no conflict is never stuck: it     *)
(* eventually leaves the active state.                                     *)
ActiveLeadsToTermination ==
    \A t \in TxId :
        (txStatus[t] = "active") ~> (txStatus[t] \in {"committed", "aborted"})

THEOREM Spec => []SIInvariants
THEOREM Spec => EveryTxStarts /\ EveryTxTerminates /\ ActiveLeadsToTermination
=============================================================================