```tla
ll back the primary (lock TTL expired)
                /\ key_lock' = [key_lock EXCEPT ![p] = {m \in @ : m.ts # t}]
                /\ key_write' = [key_write EXCEPT ![p] = Append(@, RollbackRec(t))]
    /\ UNCHANGED <<next_ts, client_vars, key_data, key_max_ts>>

Done ==
    /\ \A c \in CLIENT : client_state[c] \in {"committed", "aborted"}
    /\ UNCHANGED vars

Next ==
    \/ \E c \in CLIENT :
         \/ Start(c)
         \/ BeginPrewrite(c)
         \/ CommitPrimary(c)
         \/ FinishCommit(c)
         \/ Abort(c)
         \/ \E k \in KEY :
              \/ Read(c, k)
              \/ Prewrite(c, k)
              \/ CommitSecondary(c, k)
              \/ CleanupLock(c, k)
    \/ Done

PercolatorSpec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants *)

TypeInvariant ==
    /\ next_ts \in Nat
    /\ client_state \in [CLIENT -> States]
    /\ client_ts \in [CLIENT -> [start_ts : Nat, commit_ts : Nat]]
    /\ \A c \in CLIENT :
         /\ client_key[c].primary \in KEY
         /\ client_key[c].secondary \subseteq KEY
         /\ client_key[c].pending \subseteq KEY
    /\ DOMAIN key_lock = KEY
    /\ DOMAIN key_write = KEY
    /\ DOMAIN key_data = KEY
    /\ key_max_ts \in [KEY -> Nat]
    /\ \A k \in KEY :
         /\ key_lock[k] \subseteq LockType
         /\ key_data[k] \subseteq Nat
         /\ \A i \in DOMAIN key_write[k] : key_write[k][i] \in WriteType

\* Committed versions have data, commit_ts > start_ts, and are
\* appended in increasing commit_ts order.
WriteConsistency ==
    \A k \in KEY :
      /\ \A i \in DOMAIN key_write[k] :
           key_write[k][i].type = "write" =>
             /\ key_write[k][i].start_ts \in key_data[k]
             /\ key_write[k][i].start_ts < key_write[k][i].ts
      /\ \A i, j \in DOMAIN key_write[k] :
           (/\ i < j
            /\ key_write[k][i].type = "write"
            /\ key_write[k][j].type = "write")
             => key_write[k][i].ts < key_write[k][j].ts

\* There is at most one lock per key. A lock has data and an optimized
\* commit ts above its start ts. No lock exists for a resolved transaction.
LockConsistency ==
    \A k \in KEY :
      /\ Cardinality(key_lock[k]) <= 1
      /\ \A l \in key_lock[k] :
           /\ l.ts \in key_data[k]
           /\ l.min_commit_ts > l.ts
           /\ ~ \E i \in DOMAIN key_write[k] : key_write[k][i].start_ts = l.ts

\* A committed transaction has the same commit_ts on every key.
CommittedConsistency ==
    \A c \in CLIENT :
      LET s == StartTs(c)
          cts == client_ts[c].commit_ts
      IN
        /\ client_state[c] = "committed" =>
             \A k \in KEY :
               /\ HasWrite(k, s)
               /\ CommitTsOf(k, s) = cts
               /\ ~ HasRollback(k, s)
        /\ client_state[c] = "committing" =>
             /\ HasWrite(Primary(c), s)
             /\ \A k \in KEY :
                  /\ HasWrite(k, s) \/ OwnLocks(c, k) # {}
                  /\ HasWrite(k, s) => CommitTsOf(k, s) = cts
                  /\ ~ HasRollback(k, s)

\* An aborted transaction leaves no committed version and no lock.
AbortedConsistency ==
    \A c \in CLIENT :
      client_state[c] = "aborted" =>
        \A k \in KEY :
          /\ ~ HasWrite(k, StartTs(c))
          /\ OwnLocks(c, k) = {}

\* A rolled-back transaction is never committed on any key.
RollbackConsistency ==
    \A k \in KEY : \A i \in DOMAIN key_write[k] :
      key_write[k][i].type = "rollback" =>
        \A k2 \in KEY : ~ HasWrite(k2, key_write[k][i].start_ts)

\* Each transaction has at most one record per key.
UniqueWrite ==
    \A k \in KEY : \A i, j \in DOMAIN key_write[k] :
      key_write[k][i].start_ts = key_write[k][j].start_ts => i = j

\* No two committed transactions writing a common key overlap in time.
\* Every committed transaction commits above its start_ts.
SnapshotIsolation ==
    /\ \A c \in CLIENT :
         client_state[c] \in {"committing", "committed"} =>
           client_ts[c].commit_ts > StartTs(c)
    /\ \A a, b \in CLIENT :
         (/\ a # b
          /\ client_state[a] \in {"committing", "committed"}
          /\ client_state[b] \in {"committing", "committed"})
           => \/ client_ts[a].commit_ts < StartTs(b)
              \/ client_ts[b].commit_ts < StartTs(a)

=============================================================================
```