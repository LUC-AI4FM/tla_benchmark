```tla
  /\ ~WriteConflict(k, client_ts[c].start)
  /\ ~HasRecordWithStart(k, client_ts[c].start)

\* Prewrite a key: place lock and tentative data. Primary goes first.
Prewrite(c, k) ==
  /\ client_state[c] = "prewriting"
  /\ k \in client_key[c].pending
  /\ (k # client_key[c].primary) => (client_key[c].primary \notin client_key[c].pending)
  /\ CanPrewrite(c, k)
  /\ key_lock' = [key_lock EXCEPT ![k] =
                    {[ts |-> client_ts[c].start, primary |-> client_key[c].primary]}]
  /\ key_data' = [key_data EXCEPT ![k] = @ \cup {client_ts[c].start}]
  /\ client_key' = [client_key EXCEPT ![c].pending = @ \ {k}]
  /\ client_state' = [client_state EXCEPT ![c] =
                        IF client_key[c].pending \ {k} = {} THEN "committing" ELSE "prewriting"]
  /\ UNCHANGED <<next_ts, client_ts, client_read, key_write, key_last_read_ts>>

\* Commit the primary key: succeeds only if the primary lock still exists.
CommitPrimary(c) ==
  LET p == client_key[c].primary
      s == client_ts[c].start
  IN
  /\ client_state[c] = "committing"
  /\ HasLockEQ(p, s)
  /\ key_lock' = [key_lock EXCEPT ![p] = {}]
  /\ key_write' = [key_write EXCEPT ![p] =
                     Append(@, [start_ts |-> s, commit_ts |-> next_ts, type |-> "write"])]
  /\ client_ts' = [client_ts EXCEPT ![c].commit = next_ts]
  /\ client_state' = [client_state EXCEPT ![c] = "committed"]
  /\ next_ts' = next_ts + 1
  /\ UNCHANGED <<client_key, client_read, key_data, key_last_read_ts>>

\* The primary lock was cleaned up by someone else: the commit fails.
CommitPrimaryFail(c) ==
  /\ client_state[c] = "committing"
  /\ ~HasLockEQ(client_key[c].primary, client_ts[c].start)
  /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
  /\ UNCHANGED <<next_ts, client_ts, client_key, client_read, key_vars>>

\* Commit a secondary key after the primary is committed.
CommitSecondary(c, k) ==
  /\ client_state[c] = "committed"
  /\ k \in client_key[c].secondary
  /\ HasLockEQ(k, client_ts[c].start)
  /\ key_lock' = [key_lock EXCEPT ![k] = {}]
  /\ key_write' = [key_write EXCEPT ![k] =
                     Append(@, [start_ts |-> client_ts[c].start,
                                commit_ts |-> client_ts[c].commit,
                                type |-> "write"])]
  /\ UNCHANGED <<next_ts, client_vars, key_data, key_last_read_ts>>

\* Client aborts (or crashes) before committing; locks remain for cleanup.
Abort(c) ==
  /\ client_state[c] \in {"working", "prewriting", "committing"}
  /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
  /\ UNCHANGED <<next_ts, client_ts, client_key, client_read, key_vars>>

Next ==
  \E c \in CLIENT :
     \/ Start(c)
     \/ StartPrewrite(c)
     \/ CommitPrimary(c)
     \/ CommitPrimaryFail(c)
     \/ Abort(c)
     \/ \E k \in KEY :
          \/ Get(c, k)
          \/ CleanupLock(c, k)
          \/ Prewrite(c, k)
          \/ CommitSecondary(c, k)

PercolatorSpec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Invariants

TypeInvariant ==
  /\ next_ts \in Ts
  /\ client_state \in [CLIENT -> States]
  /\ client_ts \in [CLIENT -> [start : Nat, commit : Nat]]
  /\ client_key \in [CLIENT -> [primary : KEY, secondary : SUBSET KEY, pending : SUBSET KEY]]
  /\ \A c \in CLIENT : client_key[c].primary \notin client_key[c].secondary
  /\ \A c \in CLIENT : client_state[c] # "init" => client_ts[c].start \in Ts
  /\ \A c \in CLIENT : client_state[c] = "committed" =>
        client_ts[c].commit > client_ts[c].start
  /\ client_read \in [CLIENT -> [KEY -> Nat \cup {NotRead}]]
  /\ key_lock \in [KEY -> SUBSET LockRec]
  /\ key_write \in [KEY -> Seq(WriteRec)]
  /\ key_data \in [KEY -> SUBSET Ts]
  /\ key_last_read_ts \in [KEY -> Nat]

WriteConsistency ==
  \A k \in KEY :
    LET W == key_write[k] IN
    /\ \A i \in DOMAIN W : W[i].type = "write" => W[i].start_ts < W[i].commit_ts
    /\ \A i, j \in DOMAIN W :
         (i < j /\ W[i].type = "write" /\ W[j].type = "write")
            => W[i].commit_ts < W[j].start_ts

LockConsistency ==
  /\ \A k \in KEY : Cardinality(key_lock[k]) <= 1
  /\ \A c \in CLIENT :
       (client_state[c] = "committing" /\ HasLockEQ(client_key[c].primary, client_ts[c].start))
          => \A k \in client_key[c].secondary : HasLockEQ(k, client_ts[c].start)

CommittedConsistency ==
  \A c \in CLIENT :
    client_state[c] = "committed" =>
      LET p  == client_key[c].primary
          s  == client_ts[c].start
          w  == [start_ts |-> s, commit_ts |-> client_ts[c].commit, type |-> "write"]
      IN
      /\ \E i \in DOMAIN key_write[p] : key_write[p][i] = w
      /\ ~HasLockEQ(p, s)
      /\ s \in key_data[p]
      /\ \A k \in client_key[c].secondary :
           /\ s \in key_data[k]
           /\ \/ HasLockEQ(k, s)
              \/ \E i \in DOMAIN key_write[k] : key_write[k][i] = w

AbortedConsistency ==
  \A c \in CLIENT :
    client_state[c] = "aborted" =>
      ~HasWriteWithStart(client_key[c].primary, client_ts[c].start)

RollbackConsistency ==
  \A k1, k2 \in KEY :
    \A i \in DOMAIN key_write[k1] : \A j \in DOMAIN key_write[k2] :
      (key_write[k1][i].type = "write" /\ key_write[k2][j].type = "rollback")
         => key_write[k1][i].start_ts # key_write[k2][j].start_ts

UniqueWrite ==
  \A k \in KEY :
    \A i, j \in DOMAIN key_write[k] :
      key_write[k][i].start_ts = key_write[k][j].start_ts => i = j

\* Every recorded read observed exactly the latest version committed at or
\* before the reader's start ts; i.e. no committed write with
\* commit_ts <= read ts appears after the read was made.
SnapshotIsolation ==
  /\ \A c \in CLIENT : \A k \in KEY :
       client_read[c][k] # NotRead =>
         client_read[c][k] = LatestVisible(k, client_ts[c].start)
  /\ \A k \in KEY : key_last_read_ts[k] < next_ts

=============================================================================
```