w.ts > w.start_ts
      /\ \A w1, w2 \in key_write[k] :
           (/\ w1.type = "write" /\ w2.type = "write" /\ w1 # w2)
             => \/ w1.ts < w2.start_ts
                \/ w2.ts < w1.start_ts

\* 2. At most one lock per key; a committing txn holding its primary lock
\*    holds all of its secondary locks.
LockConsistency ==
    /\ \A k \in KEY : Cardinality(key_lock[k]) <= 1
    /\ \A c \in CLIENT :
         LET s == client_ts[c].start_ts IN
         (/\ client_state[c] = "committing"
          /\ \E l \in key_lock[CLIENT_PRIMARY[c]] : l.ts = s)
           => \A k \in CLIENT_KEY[c] : \E l \in key_lock[k] : l.ts = s

\* 3. A committed txn has its primary write and no primary lock; each
\*    secondary is committed or still holds its prewrite lock.
CommitConsistency ==
    \A c \in CLIENT :
      LET s   == client_ts[c].start_ts
          cts == client_ts[c].commit_ts
          p   == CLIENT_PRIMARY[c]
      IN
      client_state[c] = "committed" =>
        /\ [ts |-> cts, start_ts |-> s, type |-> "write"] \in key_write[p]
        /\ ~\E l \in key_lock[p] : l.ts = s
        /\ \A k \in CLIENT_KEY[c] :
             \/ [ts |-> cts, start_ts |-> s, type |-> "write"] \in key_write[k]
             \/ \E l \in key_lock[k] : l.ts = s

\* 4. An aborted txn has no committed write on its primary key.
AbortConsistency ==
    \A c \in CLIENT :
      client_state[c] = "aborted" =>
        ~\E w \in key_write[CLIENT_PRIMARY[c]] :
            /\ w.start_ts = client_ts[c].start_ts
            /\ w.type = "write"

\* 5. No txn has both committed writes and rollback records.
RollbackConsistency ==
    \A c \in CLIENT :
      LET s == client_ts[c].start_ts IN
      client_state[c] # "init" =>
        ~ /\ \E k \in AllKeys(c) : \E w \in key_write[k] :
                 w.start_ts = s /\ w.type = "write"
          /\ \E k \in AllKeys(c) : \E w \in key_write[k] :
                 w.start_ts = s /\ w.type = "rollback"

\* 6. Each start timestamp appears at most once in a key's write history.
UniqueWrite ==
    \A k \in KEY : \A w1, w2 \in key_write[k] :
      w1.start_ts = w2.start_ts => w1 = w2

\* 7. Snapshot isolation: a version observed by a reader at ts T stays the
\*    latest visible version at T (no write commits at ts <= T afterwards),
\*    and no committed write overlaps a recorded read it should have seen.
SnapshotIsolation ==
    \A c \in CLIENT : \A k \in KEY :
      client_read[c][k] # NoRead =>
        LatestVisible(k, client_ts[c].start_ts) = client_read[c][k]

Invariants ==
    /\ TypeOK
    /\ WriteConsistency
    /\ LockConsistency
    /\ CommitConsistency
    /\ AbortConsistency
    /\ RollbackConsistency
    /\ UniqueWrite
    /\ SnapshotIsolation

-------------------------------------------------------------------------
(* Liveness *)

\* Every client eventually finishes (commits or aborts).
EventuallyAllFinished ==
    <>(\A c \in CLIENT : client_state[c] \in {"committed", "aborted"})

\* Secondaries of a committed transaction are eventually resolved.
SecondariesEventuallyCommitted ==
    \A c \in CLIENT :
      (client_state[c] = "committed") ~> (client_key[c].committing = {})

THEOREM Spec => []Invariants
THEOREM Spec => EventuallyAllFinished /\ SecondariesEventuallyCommitted
=========================================================================
```