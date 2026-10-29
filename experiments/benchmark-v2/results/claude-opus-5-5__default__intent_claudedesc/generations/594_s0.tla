```tla
> StartTs(c), primary |-> CLIENT_PRIMARY[c],
                      type |-> "lock_key"]}]
  /\ client_key' = [client_key EXCEPT ![c].locking = @ \ {k}]
  /\ UNCHANGED <<next_ts, client_state, client_ts, client_read, key_write>>

\* Pessimistic: write conflict on a key still to be locked -> new for_update_ts.
RetryForUpdateTs(c) ==
  /\ c \in CLIENT_PESSIMISTIC
  /\ client_state[c] = "locking"
  /\ \E k \in client_key[c].locking :
        \E w \in WriteRecs(k) : w.ts > client_ts[c].for_update_ts
  /\ next_ts' = next_ts + 1
  /\ client_ts' = [client_ts EXCEPT ![c].for_update_ts = next_ts + 1]
  /\ UNCHANGED <<client_state, client_key, client_read, key_lock, key_write>>

\* Pessimistic: transaction was rolled back by cleanup while locking.
AbortLocking(c) ==
  /\ c \in CLIENT_PESSIMISTIC
  /\ client_state[c] = "locking"
  /\ \E k \in client_key[c].locking : RolledBack(StartTs(c), k)
  /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
  /\ UNCHANGED <<next_ts, client_ts, client_key, client_read, key_lock, key_write>>

LockingDone(c) ==
  /\ c \in CLIENT_PESSIMISTIC
  /\ client_state[c] = "locking"
  /\ client_key[c].locking = {}
  /\ client_state' = [client_state EXCEPT ![c] = "prewriting"]
  /\ client_key' = [client_key EXCEPT ![c].prewriting = CLIENT_WRITE_KEY[c]]
  /\ UNCHANGED <<next_ts, client_ts, client_read, key_lock, key_write>>

\* Pessimistic prewrite: convert own lock_key into a prewrite lock.
PrewritePessimistic(c, k) ==
  /\ c \in CLIENT_PESSIMISTIC
  /\ client_state[c] = "prewriting"
  /\ k \in client_key[c].prewriting
  /\ \E l \in key_lock[k] : l.ts = StartTs(c) /\ l.type = "lock_key"
  /\ key_lock' = [key_lock EXCEPT ![k] =
                    {[ts |-> StartTs(c), primary |-> CLIENT_PRIMARY[c],
                      type |-> "prewrite_pessimistic"]}]
  /\ client_key' = [client_key EXCEPT ![c].prewriting = @ \ {k}]
  /\ UNCHANGED <<next_ts, client_state, client_ts, client_read, key_write>>

\* Pessimistic: own lock vanished (cleaned up) -> abort.
AbortPessimisticPrewrite(c) ==
  /\ c \in CLIENT_PESSIMISTIC
  /\ client_state[c] = "prewriting"
  /\ \E k \in client_key[c].prewriting :
        ~\E l \in key_lock[k] : l.ts = StartTs(c)
  /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
  /\ UNCHANGED <<next_ts, client_ts, client_key, client_read, key_lock, key_write>>

\* Optimistic prewrite: no lock, no newer committed write, not rolled back.
PrewriteOptimistic(c, k) ==
  /\ c \in CLIENT_OPTIMISTIC
  /\ client_state[c] = "prewriting"
  /\ k \in client_key[c].prewriting
  /\ key_lock[k] = {}
  /\ ~RolledBack(StartTs(c), k)
  /\ \A w \in WriteRecs(k) : w.ts < StartTs(c)
  /\ key_lock' = [key_lock EXCEPT ![k] =
                    {[ts |-> StartTs(c), primary |-> CLIENT_PRIMARY[c],
                      type |-> "prewrite_optimistic"]}]
  /\ client_key' = [client_key EXCEPT ![c].prewriting = @ \ {k}]
  /\ UNCHANGED <<next_ts, client_state, client_ts, client_read, key_write>>

\* Optimistic: write-write conflict or rolled back -> abort.
AbortOptimisticPrewrite(c) ==
  /\ c \in CLIENT_OPTIMISTIC
  /\ client_state[c] = "prewriting"
  /\ \E k \in client_key[c].prewriting :
        \/ RolledBack(StartTs(c), k)
        \/ \E w \in WriteRecs(k) : w.ts > StartTs(c)
  /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
  /\ UNCHANGED <<next_ts, client_ts, client_key, client_read, key_lock, key_write>>

GetCommitTs(c) ==
  /\ client_state[c] = "prewriting"
  /\ client_key[c].prewriting = {}
  /\ next_ts' = next_ts + 1
  /\ client_ts' = [client_ts EXCEPT ![c].commit_ts = next_ts + 1]
  /\ client_state' = [client_state EXCEPT ![c] = "committing"]
  /\ UNCHANGED <<client_key, client_read, key_lock, key_write>>

\* Commit point: commit the primary key.
CommitPrimary(c) ==
  LET p == CLIENT_PRIMARY[c] IN
  /\ client_state[c] = "committing"
  /\ \E l \in key_lock[p] : l.ts = StartTs(c) /\ l.type # "lock_key"
  /\ key_lock' = [key_lock EXCEPT ![p] = {}]
  /\ key_write' = [key_write EXCEPT ![p] =
                     Append(@, [ts |-> client_ts[c].commit_ts,
                                start_ts |-> StartTs(c), type |-> "write"])]
  /\ client_state' = [client_state EXCEPT ![c] = "committed"]
  /\ UNCHANGED <<next_ts, client_ts, client_key, client_read>>

AbortCommit(c) ==
  LET p == CLIENT_PRIMARY[c] IN
  /\ client_state[c] = "committing"
  /\ ~\E l \in key_lock[p] : l.ts = StartTs(c)
  /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
  /\ UNCHANGED <<next_ts, client_ts, client_key, client_read, key_lock, key_write>>

-----------------------------------------------------------------------------
(* Server-side lock resolution *)

\* Secondary lock whose primary committed: commit it with the same commit_ts.
ResolveCommitted(k) ==
  \E l \in key_lock[k] :
    /\ Committed(l.ts, l.primary)
    /\ key_lock' = [key_lock EXCEPT ![k] = @ \ {l}]
    /\ key_write' = IF l.type = "lock_key" THEN key_write
                    ELSE [key_write EXCEPT ![k] =
                            Append(@, [ts |-> CommitTsOf(l.ts, l.primary),
                                       start_ts |-> l.ts, type |-> "write"])]
    /\ UNCHANGED <<next_ts, client_state, client_ts, client_key, client_read>>

\* Lock of an uncommitted transaction (TTL expired): roll back at the primary
\* and remove the lock (and the primary's lock of the same transaction).
CleanupLock(k) ==
  \E l \in key_lock[k] :
    /\ ~Committed(l.ts, l.primary)
    /\ key_lock' = [kk \in KEY |->
                      IF kk \in {k, l.primary}
                        THEN {m \in key_lock[kk] : m.ts # l.ts}
                        ELSE key_lock[kk]]
    /\ key_write' = IF RolledBack(l.ts, l.primary) THEN key_write
                    ELSE [key_write EXCEPT ![l.primary] =
                            Append(@, [ts |-> l.ts, start_ts |-> l.ts,
                                       type |-> "rollback"])]
    /\ UNCHANGED <<next_ts, client_state, client_ts, client_key, client_read>>

-----------------------------------------------------------------------------
AllDone ==
  /\ \A c \in CLIENT : client_state[c] \in {"committed", "aborted"}
  /\ \A k \in KEY : key_lock[k] = {}

Terminating == AllDone /\ UNCHANGED vars

ClientNext ==
  \E c \in CLIENT :
    \/ Start(c)
    \/ \E k \in KEY : ReadKey(c, k)
    \/ FinishReading(c)
    \/ \E k \in KEY : LockKey(c, k)
    \/ RetryForUpdateTs(c)
    \/ AbortLocking(c)
    \/ LockingDone(c)
    \/ \E k \in KEY : PrewritePessimistic(c, k)
    \/ AbortPessimisticPrewrite(c)
    \/ \E k \in KEY : PrewriteOptimistic(c, k)
    \/ AbortOptimisticPrewrite(c)
    \/ GetCommitTs(c)
    \/ CommitPrimary(c)
    \/ AbortCommit(c)

ServerNext == \E k \in KEY : ResolveCommitted(k) \/ CleanupLock(k)

Next == ClientNext \/ ServerNext \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(ClientNext) /\ WF_vars(ServerNext)

-----------------------------------------------------------------------------
(* Safety *)

\* At most one lock per key (mutual exclusion).
OneLockPerKey == \A k \in KEY : Cardinality(key_lock[k]) <= 1

\* Committed writes on each key are totally ordered by commit_ts.
WriteSeriesOrdered ==
  \A k \in KEY : \A i, j \in DOMAIN key_write[k] :
    (i < j /\ key_write[k][i].type = "write" /\ key_write[k][j].type = "write")
      => key_write[k][i].ts < key_write[k][j].ts

\* Isolation / conflict resolution: no committed write of another transaction
\* falls between a committer's for_update_ts (= start_ts for optimistic) and
\* its commit_ts on any key it wrote.
NoWriteWriteConflict ==
  \A c \in CLIENT : \A k \in CLIENT_WRITE_KEY[c] :
    (client_state[c] # "init" /\ Committed(StartTs(c), k)) =>
      \A w \in WriteRecs(k) :
        w.start_ts # StartTs(c) =>
          ~(client_ts[c].for_update_ts < w.ts /\ w.ts < client_ts[c].commit_ts)

\* Snapshot isolation of reads: the value read remains the latest committed
\* value visible at start_ts (no partial/late-appearing results).
SnapshotRead ==
  \A c \in CLIENT :
    client_state[c] # "init" =>
      \A k \in CLIENT_READ_KEY[c] \ client_key[c].reading :
        client_read[c][k] = VisibleValue(k, StartTs(c))

\* Atomicity: a transaction is never both committed and rolled back.
Atomicity ==
  \A c \in CLIENT : client_state[c] # "init" =>
    LET ts == StartTs(c) IN
    /\ ~((\E k \in KEY : Committed(ts, k)) /\ (\E k \in KEY : RolledBack(ts, k)))
    /\ client_state[c] = "committed" => \A k \in KEY : ~RolledBack(ts, k)
    /\ client_state[c] = "aborted"   => \A k \in KEY : ~Committed(ts, k)

\* No lost updates: every write key of a committed transaction is either
\* committed or still covered by its lock (pending resolution).
NoLostUpdate ==
  \A c \in CLIENT :
    client_state[c] = "committed" =>
      \A k \in CLIENT_WRITE_KEY[c] :
        \/ Committed(StartTs(c), k)
        \/ \E l \in key_lock[k] : l.ts = StartTs(c)

Invariants ==
  /\ TypeOK
  /\ OneLockPerKey
  /\ WriteSeriesOrdered
  /\ NoWriteWriteConflict
  /\ SnapshotRead
  /\ Atomicity
  /\ NoLostUpdate

(* Liveness *)

AllClientsTerminate ==
  <>(\A c \in CLIENT : client_state[c] \in {"committed", "aborted"})

LocksEventuallyResolved == <>[](\A k \in KEY : key_lock[k] = {})

CommittedEventuallyDurable ==
  \A c \in CLIENT :
    (client_state[c] = "committed") ~>
      (\A k \in CLIENT_WRITE_KEY[c] : Committed(StartTs(c), k))

THEOREM Spec => []Invariants
=============================================================================
```