------------------------------------------------
Next ==
  \/ \E c \in CLIENT :
       \/ ClientLockKey(c)
       \/ ClientPrewrite(c)
       \/ ClientAbort(c)
       \/ ClientCommitted(c)
       \/ ClientCommitFailed(c)
       \/ \E k \in KEY :
            \/ ClientLockedKey(c, k)
            \/ ClientRetryLockKey(c, k)
            \/ ClientPrewrited(c, k)
  \/ \E m \in msg_reqs :
       \/ ServerLockKey(m)
       \/ ServerPrewriteOptimistic(m)
       \/ ServerPrewritePessimistic(m)
       \/ ServerCommit(m)
       \/ ServerCheckTxnStatus(m)
       \/ \E k \in KEY :
            \/ ServerResolveRollbacked(m, k)
            \/ ServerResolveCommitted(m, k)
  \/ \E k \in KEY : ServerCleanupStaleLock(k)

\* Safety-focused specification: no fairness conditions.
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Safety invariants

TypeOK ==
  /\ next_ts \in Nat \ {0}
  /\ client_state \in [CLIENT -> ClientStates]
  /\ client_ts \in [CLIENT -> [start_ts : Nat, commit_ts : Nat, for_update_ts : Nat]]
  /\ client_key \in [CLIENT -> [locking : SUBSET KEY, prewriting : SUBSET KEY]]
  /\ \A k \in KEY :
       /\ key_lock[k] \subseteq [ts : Nat, primary : KEY, type : LockTypes]
       /\ key_write[k] \subseteq [ts : Nat, start_ts : Nat, type : WriteTypes]
       /\ key_data[k] \subseteq Nat
  /\ msg_reqs \subseteq [type : MsgTypes, start_ts : Nat, primary : KEY, key : KEY,
                         commit_ts : Nat, for_update_ts : Nat]

\* A committed transaction has its commit record on the primary and no rollback anywhere.
CommittedConsistency ==
  \A c \in CLIENT : client_state[c] = "committed" =>
    /\ [ts |-> client_ts[c].commit_ts, start_ts |-> client_ts[c].start_ts, type |-> "write"]
         \in key_write[CLIENT_PRIMARY[c]]
    /\ \A k \in KEY : ~HasRollback(k, client_ts[c].start_ts)

\* An aborted transaction has no commit record on any key.
AbortedConsistency ==
  \A c \in CLIENT : client_state[c] = "aborted" =>
    \A k \in KEY : ~HasCommit(k, client_ts[c].start_ts)

\* A transaction is never both committed and rolled back on any key.
CommitAbortConsistency ==
  \A k1, k2 \in KEY : \A w1 \in key_write[k1], w2 \in key_write[k2] :
    (w1.start_ts = w2.start_ts) => (w1.type = w2.type)

\* Locks never coexist with a write record of the same transaction on the same key;
\* prewrite locks and committed writes always have data.
LockWriteConsistency ==
  \A k \in KEY :
    /\ \A l \in key_lock[k] : ~HasWriteWithStart(k, l.ts)
    /\ \A l \in key_lock[k] : l.type # "lock_key" => l.ts \in key_data[k]
    /\ \A w \in key_write[k] : w.type = "write" => w.start_ts \in key_data[k]

UniqueLockPerKey ==
  \A k \in KEY : Cardinality(key_lock[k]) <= 1

UniqueWrite ==
  \A k \in KEY : \A w1, w2 \in key_write[k] :
    /\ (w1.ts = w2.ts) => (w1 = w2)
    /\ (w1.start_ts = w2.start_ts) => (w1 = w2)

UniqueStartTs ==
  \A c1, c2 \in CLIENT :
    (c1 # c2 /\ client_state[c1] # "init" /\ client_state[c2] # "init")
      => client_ts[c1].start_ts # client_ts[c2].start_ts

MsgTsConsistency ==
  \A m \in msg_reqs :
    /\ 0 < m.start_ts /\ m.start_ts < next_ts
    /\ m.for_update_ts < next_ts
    /\ m.type = "lock_key" => m.start_ts <= m.for_update_ts
    /\ m.type \in {"commit", "resolve_committed"} =>
         /\ m.start_ts < m.commit_ts
         /\ m.commit_ts < next_ts

\* No other transaction committed a write to an optimistic transaction's keys
\* between its start_ts and commit_ts.
OptimisticSnapshotIsolation ==
  \A c \in OPTIMISTIC_CLIENT : client_state[c] = "committed" =>
    \A k \in CLIENT_KEY[c] : \A w \in key_write[k] :
      (w.type = "write" /\ w.start_ts # client_ts[c].start_ts) =>
        ~(client_ts[c].start_ts < w.ts /\ w.ts < client_ts[c].commit_ts)

\* No other transaction committed a write to a pessimistic transaction's keys
\* between its (final) for_update_ts and commit_ts.
PessimisticSnapshotIsolation ==
  \A c \in PESSIMISTIC_CLIENT : client_state[c] = "committed" =>
    \A k \in CLIENT_KEY[c] : \A w \in key_write[k] :
      (w.type = "write" /\ w.start_ts # client_ts[c].start_ts) =>
        ~(client_ts[c].for_update_ts < w.ts /\ w.ts < client_ts[c].commit_ts)

SafetyInvariant ==
  /\ TypeOK
  /\ CommittedConsistency
  /\ AbortedConsistency
  /\ CommitAbortConsistency
  /\ LockWriteConsistency
  /\ UniqueLockPerKey
  /\ UniqueWrite
  /\ UniqueStartTs
  /\ MsgTsConsistency
  /\ OptimisticSnapshotIsolation
  /\ PessimisticSnapshotIsolation

THEOREM Spec => []SafetyInvariant
=============================================================================
```