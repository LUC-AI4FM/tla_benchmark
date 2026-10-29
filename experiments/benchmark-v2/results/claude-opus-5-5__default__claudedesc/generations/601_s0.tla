```tla
AbortPrewrite(c) ==
  /\ client_state[c] = "prewriting"
  /\ client_key[c].pending = {}
  /\ ~HasLock(client_key[c].primary, client_ts[c].start_ts)
  /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
  /\ UNCHANGED <<next_ts, client_ts, client_key, key_lock, key_write,
                 key_data, key_max_ts>>

\* Commit a secondary key (or observe it was already rolled forward).
CommitSecondary(c, k) ==
  LET start == client_ts[c].start_ts
      cts   == client_ts[c].commit_ts
  IN
  /\ client_state[c] = "committing"
  /\ k \in client_key[c].pending
  /\ IF HasLock(k, start)
       THEN /\ key_lock' = [key_lock EXCEPT ![k] =
                              {l \in key_lock[k] : l.ts # start}]
            /\ key_write' = [key_write EXCEPT ![k] =
                               Append(key_write[k],
                                      [ts |-> cts, start_ts |-> start,
                                       type |-> "write"])]
       ELSE UNCHANGED <<key_lock, key_write>>
  /\ client_key' = [client_key EXCEPT ![c].pending =
                      client_key[c].pending \ {k}]
  /\ client_state' = [client_state EXCEPT ![c] =
                        IF client_key[c].pending = {k} THEN "committed"
                                                       ELSE "committing"]
  /\ UNCHANGED <<next_ts, client_ts, key_data, key_max_ts>>

\* Lock resolution performed by any client encountering a stale lock.
\*  - A primary lock may be rolled back (its owner is presumed dead).
\*  - A secondary lock is rolled forward if its primary is committed,
\*    otherwise rolled back (also writing a rollback on the primary if
\*    the primary has no record yet). It must wait while the primary
\*    lock is still present.
Cleanup(k) ==
  \E l \in key_lock[k] :
    LET p  == l.primary
        t  == l.ts
        rb == [ts |-> t, start_ts |-> t, type |-> "rollback"]
    IN
    /\ IF k = p
         THEN /\ key_lock' = [key_lock EXCEPT ![k] = key_lock[k] \ {l}]
              /\ key_write' = [key_write EXCEPT ![k] = Append(key_write[k], rb)]
         ELSE /\ ~HasLock(p, t)
              /\ IF CommitRecs(p, t) # {}
                   THEN LET w == CHOOSE x \in CommitRecs(p, t) : TRUE IN
                        /\ key_lock' = [key_lock EXCEPT ![k] = key_lock[k] \ {l}]
                        /\ key_write' = [key_write EXCEPT ![k] =
                                           Append(key_write[k],
                                                  [ts |-> w.ts, start_ts |-> t,
                                                   type |-> "write"])]
                   ELSE /\ key_lock' = [key_lock EXCEPT ![k] = key_lock[k] \ {l}]
                        /\ key_write' = [key_write EXCEPT
                                           ![k] = Append(key_write[k], rb),
                                           ![p] = IF FindWrite(p, t) = {}
                                                    THEN Append(key_write[p], rb)
                                                    ELSE key_write[p]]
    /\ UNCHANGED <<next_ts, client_state, client_ts, client_key,
                   key_data, key_max_ts>>

\* All transactions have finished: allow stuttering to avoid deadlock.
Terminated ==
  /\ \A c \in CLIENT : client_state[c] \in {"committed", "aborted"}
  /\ \A k \in KEY : key_lock[k] = {}
  /\ UNCHANGED vars

Next ==
  \/ \E c \in CLIENT :
       \/ Start(c)
       \/ BeginPrewrite(c)
       \/ Commit(c)
       \/ AbortPrewrite(c)
  \/ \E c \in CLIENT, k \in KEY :
       \/ Get(c, k)
       \/ Prewrite(c, k)
       \/ CommitSecondary(c, k)
  \/ \E k \in KEY : Cleanup(k)
  \/ Terminated

PercolatorSpec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety invariants *)

WriteConsistency ==
  /\ \A k \in KEY : \A w \in WritesOf(k) :
       /\ w.type = "write"    => (w.ts > w.start_ts /\ w.start_ts \in key_data[k])
       /\ w.type = "rollback" => w.ts = w.start_ts
  /\ \A k1, k2 \in KEY :
       \A w1 \in WritesOf(k1), w2 \in WritesOf(k2) :
         (w1.type = "write" /\ w2.type = "write" /\ w1.start_ts = w2.start_ts)
           => w1.ts = w2.ts

LockConsistency ==
  \A k \in KEY :
    /\ Cardinality(key_lock[k]) <= 1
    /\ \A l \in key_lock[k] :
         /\ l.ts \in key_data[k]
         /\ l.min_commit_ts > l.ts
         /\ FindWrite(k, l.ts) = {}

CommittedConsistency ==
  \A c \in CLIENT :
    LET start == client_ts[c].start_ts
        cts   == client_ts[c].commit_ts
        p     == client_key[c].primary
    IN
    /\ client_state[c] \in {"committing", "committed"} =>
         \E w \in CommitRecs(p, start) : w.ts = cts
    /\ client_state[c] = "committed" =>
         \A k \in KEY :
           /\ ~HasLock(k, start)
           /\ \E w \in CommitRecs(k, start) : w.ts = cts

AbortedConsistency ==
  \A c \in CLIENT :
    client_state[c] = "aborted" =>
      \A k \in KEY : CommitRecs(k, client_ts[c].start_ts) = {}

RollbackConsistency ==
  \A k1, k2 \in KEY :
    \A w1 \in WritesOf(k1), w2 \in WritesOf(k2) :
      (w1.type = "rollback" /\ w2.type = "write") => w1.start_ts # w2.start_ts

UniqueWrite ==
  \A k \in KEY :
    \A i, j \in 1..Len(key_write[k]) :
      i # j => key_write[k][i].start_ts # key_write[k][j].start_ts

\* Write-write conflict freedom: committed writers of the same key never
\* have overlapping [start_ts, commit_ts] intervals.
SnapshotIsolation ==
  \A k \in KEY :
    \A w1, w2 \in WritesOf(k) :
      (/\ w1.type = "write"
       /\ w2.type = "write"
       /\ w1.start_ts # w2.start_ts)
        => (w1.ts < w2.start_ts \/ w2.ts < w1.start_ts)

THEOREM PercolatorSpec => [](/\ TypeInvariant
                             /\ WriteConsistency
                             /\ LockConsistency
                             /\ CommittedConsistency
                             /\ AbortedConsistency
                             /\ RollbackConsistency
                             /\ UniqueWrite
                             /\ SnapshotIsolation)
=============================================================================
```