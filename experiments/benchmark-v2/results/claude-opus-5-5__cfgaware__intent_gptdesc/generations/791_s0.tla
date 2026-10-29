------------------------------- MODULE MVKVStore -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Key, Val, TxId, NoVal

ASSUME NoVal \notin Val
ASSUME IsFiniteSet(TxId) /\ IsFiniteSet(Key)

VARIABLES
    store,      \* store[k] : set of committed versions [ts |-> n, val |-> v]
    clock,      \* logical commit clock; all versions with ts <= clock are visible
    status,     \* status[t] \in {"idle","active","committed","aborted"}
    snap,       \* snap[t] : snapshot timestamp acquired at Begin
    readKeys,   \* readKeys[t] : keys read from the snapshot
    readVal,    \* readVal[t][k] : value observed by snapshot read of k
    writeBuf,   \* writeBuf[t][k] : buffered write, NoVal = not written
    commitTs    \* commitTs[t] : commit identifier (0 = none)

vars == <<store, clock, status, snap, readKeys, readVal, writeBuf, commitTs>>

MaxTs  == Cardinality(TxId)
TsRange == 0..MaxTs
VVal   == Val \cup {NoVal}
Status == {"idle", "active", "committed", "aborted"}
Version == [ts : TsRange, val : VVal]

\* ---------------------------------------------------------------------------
\* Helpers
\* ---------------------------------------------------------------------------
LatestBefore(k, ts) ==
    LET vs == {v \in store[k] : v.ts <= ts}
    IN  CHOOSE v \in vs : \A w \in vs : w.ts <= v.ts

ValueAt(k, ts) == LatestBefore(k, ts).val

LatestTs(k) == LatestBefore(k, clock).ts

WrittenKeys(t) == {k \in Key : writeBuf[t][k] # NoVal}

\* Value a transaction sees for key k (read-your-own-writes, else snapshot)
TxView(t, k) == IF writeBuf[t][k] # NoVal THEN writeBuf[t][k]
                                          ELSE ValueAt(k, snap[t])

\* Conflict validation: no key read or written by t was overwritten by
\* a transaction that committed after t's snapshot (first-committer-wins
\* on writes plus read validation => serializable in commit order).
NoConflict(t) ==
    \A k \in readKeys[t] \cup WrittenKeys(t) : LatestTs(k) <= snap[t]

\* ---------------------------------------------------------------------------
\* Initial state
\* ---------------------------------------------------------------------------
Init ==
    /\ store    = [k \in Key |-> {[ts |-> 0, val |-> NoVal]}]
    /\ clock    = 0
    /\ status   = [t \in TxId |-> "idle"]
    /\ snap     = [t \in TxId |-> 0]
    /\ readKeys = [t \in TxId |-> {}]
    /\ readVal  = [t \in TxId |-> [k \in Key |-> NoVal]]
    /\ writeBuf = [t \in TxId |-> [k \in Key |-> NoVal]]
    /\ commitTs = [t \in TxId |-> 0]

\* ---------------------------------------------------------------------------
\* Phase 1: acquire a snapshot
\* ---------------------------------------------------------------------------
Begin(t) ==
    /\ status[t] = "idle"
    /\ status' = [status EXCEPT ![t] = "active"]
    /\ snap'   = [snap EXCEPT ![t] = clock]
    /\ UNCHANGED <<store, clock, readKeys, readVal, writeBuf, commitTs>>

\* ---------------------------------------------------------------------------
\* Phase 2: reads and writes against the snapshot
\* ---------------------------------------------------------------------------
\* Snapshot read (reads of own buffered writes are served locally and
\* do not touch the store, hence are not recorded).
Read(t, k) ==
    /\ status[t] = "active"
    /\ k \notin readKeys[t]
    /\ writeBuf[t][k] = NoVal
    /\ readKeys' = [readKeys EXCEPT ![t] = @ \cup {k}]
    /\ readVal'  = [readVal EXCEPT ![t][k] = ValueAt(k, snap[t])]
    /\ UNCHANGED <<store, clock, status, snap, writeBuf, commitTs>>

Write(t, k, v) ==
    /\ status[t] = "active"
    /\ writeBuf[t][k] = NoVal
    /\ writeBuf' = [writeBuf EXCEPT ![t][k] = v]
    /\ UNCHANGED <<store, clock, status, snap, readKeys, readVal, commitTs>>

\* ---------------------------------------------------------------------------
\* Phase 3: atomic commit at a single logical commit point
\* ---------------------------------------------------------------------------
Commit(t) ==
    /\ status[t] = "active"
    /\ NoConflict(t)
    /\ clock' = clock + 1
    /\ commitTs' = [commitTs EXCEPT ![t] = clock + 1]
    /\ store' = [k \in Key |->
                   IF writeBuf[t][k] # NoVal
                   THEN store[k] \cup {[ts |-> clock + 1, val |-> writeBuf[t][k]]}
                   ELSE store[k]]
    /\ status' = [status EXCEPT ![t] = "committed"]
    /\ UNCHANGED <<snap, readKeys, readVal, writeBuf>>

\* Conflict resolution: a transaction that fails validation is aborted
ConflictAbort(t) ==
    /\ status[t] = "active"
    /\ ~NoConflict(t)
    /\ status' = [status EXCEPT ![t] = "aborted"]
    /\ UNCHANGED <<store, clock, snap, readKeys, readVal, writeBuf, commitTs>>

\* Voluntary client abort
ClientAbort(t) ==
    /\ status[t] = "active"
    /\ status' = [status EXCEPT ![t] = "aborted"]
    /\ UNCHANGED <<store, clock, snap, readKeys, readVal, writeBuf, commitTs>>

\* Terminal stuttering once all transactions finished (avoids spurious deadlock)
Done ==
    /\ \A t \in TxId : status[t] \in {"committed", "aborted"}
    /\ UNCHANGED vars

Next ==
    \/ \E t \in TxId :
          \/ Begin(t)
          \/ \E k \in Key : Read(t, k)
          \/ \E k \in Key, v \in Val : Write(t, k, v)
          \/ Commit(t)
          \/ ConflictAbort(t)
          \/ ClientAbort(t)
    \/ Done

\* Liveness: a nonfaulty active client eventually finishes (commits or is
\* resolved by conflict abort); no fairness on Begin/Read/Write.
Fairness == \A t \in TxId : WF_vars(Commit(t) \/ ConflictAbort(t))

Spec == Init /\ [][Next]_vars /\ Fairness

\* ---------------------------------------------------------------------------
\* Invariants
\* ---------------------------------------------------------------------------
TypeInvariant ==
    /\ store    \in [Key -> SUBSET Version]
    /\ clock    \in TsRange
    /\ status   \in [TxId -> Status]
    /\ snap     \in [TxId -> TsRange]
    /\ readKeys \in [TxId -> SUBSET Key]
    /\ readVal  \in [TxId -> [Key -> VVal]]
    /\ writeBuf \in [TxId -> [Key -> VVal]]
    /\ commitTs \in [TxId -> TsRange]

TxLifecycle ==
    \A t \in TxId :
        /\ status[t] = "idle" =>
              /\ snap[t] = 0 /\ readKeys[t] = {}
              /\ WrittenKeys(t) = {} /\ commitTs[t] = 0
        /\ (status[t] = "committed") <=> (commitTs[t] > 0)
        /\ status[t] # "idle" => snap[t] <= clock
        /\ status[t] = "committed" => snap[t] < commitTs[t] /\ commitTs[t] <= clock

\* Commit identifiers are unique
UniqueCommitIds ==
    \A t1, t2 \in TxId :
        (t1 # t2 /\ commitTs[t1] > 0) => commitTs[t1] # commitTs[t2]

\* Version monotonicity: per key, at most one version per timestamp,
\* all versions are at or below the visibility clock, initial version kept.
VersionMonotonicity ==
    \A k \in Key :
        /\ [ts |-> 0, val |-> NoVal] \in store[k]
        /\ \A v, w \in store[k] : v.ts = w.ts => v = w
        /\ \A v \in store[k] : v.ts <= clock

\* Atomicity: a committed transaction's writes are all visible at exactly
\* its commit point; nothing else ever appears; aborted writes never appear.
Atomicity ==
    /\ \A t \in TxId : status[t] = "committed" =>
          \A k \in Key :
             (writeBuf[t][k] # NoVal) <=>
                ([ts |-> commitTs[t], val |-> writeBuf[t][k]] \in store[k])
    /\ \A k \in Key : \A v \in store[k] : v.ts > 0 =>
          \E t \in TxId : /\ status[t] = "committed"
                          /\ commitTs[t] = v.ts
                          /\ writeBuf[t][k] = v.val

\* Snapshot isolation: every snapshot read reflects the single snapshot
SnapshotIsolation ==
    \A t \in TxId : status[t] # "idle" =>
        \A k \in readKeys[t] : readVal[t][k] = ValueAt(k, snap[t])

\* Serializability: each committed transaction's reads equal the state
\* immediately before its commit point, so the execution is equivalent to
\* the serial execution in commit-timestamp order.
Serializability ==
    \A t \in TxId : status[t] = "committed" =>
        \A k \in readKeys[t] : readVal[t][k] = ValueAt(k, commitTs[t] - 1)

\* No read observes a version that was not committed/visible at snapshot time
CausalVisibility ==
    \A t \in TxId : status[t] # "idle" =>
        \A k \in readKeys[t] : LatestBefore(k, snap[t]).ts <= snap[t]

Safety ==
    /\ TypeInvariant /\ TxLifecycle /\ UniqueCommitIds /\ VersionMonotonicity
    /\ Atomicity /\ SnapshotIsolation /\ Serializability /\ CausalVisibility

\* ---------------------------------------------------------------------------
\* Temporal properties
\* ---------------------------------------------------------------------------
StoreMonotonic ==
    [][\A k \in Key : store[k] \subseteq store'[k]]_vars

ClockMonotonic == [][clock' >= clock]_vars

Progress == \A t \in TxId : (status[t] = "active") ~> (status[t] \in {"committed", "aborted"})

=============================================================================