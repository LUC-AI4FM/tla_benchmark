all write keys.
ClientStartOptimistic(c) ==
  /\ c \in OPTIMISTIC_CLIENT
  /\ client_state[c] = "init"
  /\ client_state' = [client_state EXCEPT ![c] = "prewriting"]
  /\ client_ts' = [client_ts EXCEPT ![c].start_ts = next_ts]
  /\ client_key' = [client_key EXCEPT ![c].prewriting = CLIENT_WRITE_KEY[c]]
  /\ msg_reqs' = msg_reqs \cup
       {[c |-> c, type |-> "prewrite_optimistic", start_ts |-> next_ts,
         primary |-> CLIENT_PRIMARY[c], key |-> k] : k \in CLIENT_WRITE_KEY[c]}
  /\ next_ts' = next_ts + 1
  /\ UNCHANGED key_vars

\* Pessimistic client obtains start_ts (= initial for_update_ts) and
\* sends pessimistic lock requests for all write keys.
ClientStartPessimistic(c) ==
  /\ c \in PESSIMISTIC_CLIENT
  /\ client_state[c] = "init"
  /\ client_state' = [client_state EXCEPT ![c] = "locking"]
  /\ client_ts' = [client_ts EXCEPT ![c].start_ts = next_ts,
                                    ![c].for_update_ts = next_ts]
  /\ client_key' = [client_key EXCEPT ![c].locking = CLIENT_WRITE_KEY[c]]
  /\ msg_reqs' = msg_reqs \cup
       {[c |-> c, type |-> "lock_key", start_ts |-> next_ts,
         primary |-> CLIENT_PRIMARY[c], key |-> k,
         for_update_ts |-> next_ts] : k \in CLIENT_WRITE_KEY[c]}
  /\ next_ts' = next_ts + 1
  /\ UNCHANGED key_vars

\* All pessimistic locks acquired: send pessimistic prewrites.
ClientPrewritePessimistic(c) ==
  /\ c \in PESSIMISTIC_CLIENT
  /\ client_state[c] = "locking"
  /\ client_key[c].locking = {}
  /\ client_state' = [client_state EXCEPT ![c] = "prewriting"]
  /\ client_key' = [client_key EXCEPT ![c].prewriting = CLIENT_WRITE_KEY[c]]
  /\ msg_reqs' = msg_reqs \cup
       {[c |-> c, type |-> "prewrite_pessimistic",
         start_ts |-> client_ts[c].start_ts,
         primary |-> CLIENT_PRIMARY[c], key |-> k] : k \in CLIENT_WRITE_KEY[c]}
  /\ UNCHANGED <<next_ts, client_ts, key_vars>>

\* All prewrites succeeded: obtain commit_ts and commit the primary.
ClientCommit(c) ==
  /\ client_state[c] = "prewriting"
  /\ client_key[c].prewriting = {}
  /\ client_state' = [client_state EXCEPT ![c] = "committing"]
  /\ client_ts' = [client_ts EXCEPT ![c].commit_ts = next_ts]
  /\ msg_reqs' = msg_reqs \cup
       {[c |-> c, type |-> "commit", start_ts |-> client_ts[c].start_ts,
         primary |-> CLIENT_PRIMARY[c], commit_ts |-> next_ts]}
  /\ next_ts' = next_ts + 1
  /\ UNCHANGED <<client_key, key_vars>>

\* Any client encountering a lock may ask for the status of its owner
\* transaction (TTL is abstracted as always expired).
ClientCheckTxnStatus ==
  \E k \in KEY : \E l \in key_lock[k] :
    LET m == [type |-> "check_txn_status", start_ts |-> l.ts,
              primary |-> l.primary]
    IN /\ m \notin msg_reqs
       /\ msg_reqs' = msg_reqs \cup {m}
       /\ UNCHANGED <<next_ts, client_vars, key_vars>>

-----------------------------------------------------------------------------
\* Server actions (responses handled atomically on the client side)

ServerLockKey ==
  \E m \in msg_reqs :
    /\ m.type = "lock_key"
    /\ LET c == m.c
           k == m.key
           s == m.start_ts
       IN
       /\ client_state[c] = "locking"
       /\ k \in client_key[c].locking
       /\ m.for_update_ts = client_ts[c].for_update_ts
       /\ \/ \* already locked by this transaction
             /\ HasOwnLock(k, s)
             /\ client_key' = [client_key EXCEPT ![c].locking = @ \ {k}]
             /\ UNCHANGED <<next_ts, client_state, client_ts, msg_reqs,
                            key_vars>>
          \/ \* transaction already rolled back on this key
             /\ key_lock[k] = {}
             /\ HasRecord(k, s)
             /\ Abort(c)
             /\ UNCHANGED <<next_ts, client_ts, client_key, msg_reqs,
                            key_vars>>
          \/ \* write conflict: retry with a fresh for_update_ts
             /\ key_lock[k] = {}
             /\ ~HasRecord(k, s)
             /\ \E w \in WriteRecs(k) :
                  w.type = "write" /\ w.ts > m.for_update_ts
             /\ client_ts' = [client_ts EXCEPT ![c].for_update_ts = next_ts]
             /\ msg_reqs' = msg_reqs \cup
                  {[c |-> c, type |-> "lock_key", start_ts |-> s,
                    primary |-> m.primary, key |-> kk,
                    for_update_ts |-> next_ts] : kk \in client_key[c].locking}
             /\ next_ts' = next_ts + 1
             /\ UNCHANGED <<client_state, client_key, key_vars>>
          \/ \* acquire the pessimistic lock
             /\ key_lock[k] = {}
             /\ ~HasRecord(k, s)
             /\ ~\E w \in WriteRecs(k) :
                   w.type = "write" /\ w.ts > m.for_update_ts
             /\ key_lock' = [key_lock EXCEPT ![k] =
                  {[ts |-> s, primary |-> m.primary, type |-> "lock_key"]}]
             /\ client_key' = [client_key EXCEPT ![c].locking = @ \ {k}]
             /\ UNCHANGED <<next_ts, client_state, client_ts, msg_reqs,
                            key_write, key_data>>

ServerPrewriteOptimistic ==
  \E m \in msg_reqs :
    /\ m.type = "prewrite_optimistic"
    /\ LET c == m.c
           k == m.key
           s == m.start_ts
       IN
       /\ client_state[c] = "prewriting"
       /\ k \in client_key[c].prewriting
       /\ \/ /\ HasOwnLock(k, s)
             /\ client_key' = [client_key EXCEPT ![c].prewriting = @ \ {k}]
             /\ UNCHANGED <<next_ts, client_state, client_ts, msg_reqs,
                            key_vars>>
          \/ /\ key_lock[k] = {}
             /\ \/ HasRecord(k, s)
                \/ \E w \in WriteRecs(k) : w.type = "write" /\ w.ts > s
             /\ Abort(c)
             /\ UNCHANGED <<next_ts, client_ts, client_key, msg_reqs,
                            key_vars>>
          \/ /\ key_lock[k] = {}
             /\ ~HasRecord(k, s)
             /\ ~\E w \in WriteRecs(k) : w.type = "write" /\ w.ts > s
             /\ key_lock' = [key_lock EXCEPT ![k] =
                  {[ts |-> s, primary |-> m.primary,
                    type |-> "prewrite_optimistic"]}]
             /\ key_data' = [key_data EXCEPT ![k] = @ \cup {s}]
             /\ client_key' = [client_key EXCEPT ![c].prewriting = @ \ {k}]
             /\ UNCHANGED <<next_ts, client_state, client_ts, msg_reqs,
                            key_write>>

ServerPrewritePessimistic ==
  \E m \in msg_reqs :
    /\ m.type = "prewrite_pessimistic"
    /\ LET c == m.c
           k == m.key
           s == m.start_ts
       IN
       /\ client_state[c] = "prewriting"
       /\ k \in client_key[c].prewriting
       /\ \/ \E l \in key_lock[k] :
                /\ l.ts = s
                /\ l.type = "lock_key"
                /\ key_lock' = [key_lock EXCEPT ![k] =
                     {[ts |-> s, primary |-> l.primary,
                       type |-> "prewrite_pessimistic"]}]
                /\ key_data' = [key_data EXCEPT ![k] = @ \cup {s}]
                /\ client_key' = [client_key EXCEPT ![c].prewriting = @ \ {k}]
                /\ UNCHANGED <<next_ts, client_state, client_ts, msg_reqs,
                               key_write>>
          \/ /\ \E l \in key_lock[k] :
                  l.ts = s /\ l.type = "prewrite_pessimistic"
             /\ client_key' = [client_key EXCEPT ![c].prewriting = @ \ {k}]
             /\ UNCHANGED <<next_ts, client_state, client_ts, msg_reqs,
                            key_vars>>
          \/ \* pessimistic lock was lost (rolled back): abort
             /\ ~HasOwnLock(k, s)
             /\ Abort(c)
             /\ UNCHANGED <<next_ts, client_ts, client_key, msg_reqs,
                            key_vars>>

ServerCommit ==
  \E m \in msg_reqs :
    /\ m.type = "commit"
    /\ LET c == m.c
           k == m.primary
           s == m.start_ts
       IN
       /\ client_state[c] = "committing"
       /\ m.commit_ts = client_ts[c].commit_ts
       /\ \/ /\ HasOwnLock(k, s)
             /\ key_lock' = [key_lock EXCEPT ![k] = {}]
             /\ key_write' = [key_write EXCEPT ![k] = Append(@,
                  [ts |-> m.commit_ts, start_ts |-> s, type |-> "write"])]
             /\ client_state' = [client_state EXCEPT ![c] = "committed"]
             /\ msg_reqs' = msg_reqs \cup
                  {[type |-> "resolve_committed", start_ts |-> s,
                    primary |-> k, commit_ts |-> m.commit_ts]}
             /\ UNCHANGED <<next_ts, client_ts, client_key, key_data>>
          \/ /\ ~HasOwnLock(k, s)
             /\ Abort(c)
             /\ UNCHANGED <<next_ts, client_ts, client_key, msg_reqs,
                            key_vars>>

ServerCheckTxnStatus ==
  \E m \in msg_reqs :
    /\ m.type = "check_txn_status"
    /\ LET k == m.primary
           s == m.start_ts
           rb == [type |-> "resolve_rollbacked", start_ts |-> s, primary |-> k]
       IN
       \/ \* lock found and TTL expired: roll back the primary
          /\ HasOwnLock(k, s)
          /\ key_lock' = [key_lock EXCEPT ![k] = {}]
          /\ key_write' = [key_write EXCEPT ![k] = Append(@,
               [ts |-> s, start_ts |-> s, type |-> "rollback"])]
          /\ msg_reqs' = msg_reqs \cup {rb}
          /\ UNCHANGED <<next_ts, client_vars, key_data>>
       \/ \* already committed
          /\ ~HasOwnLock(k, s)
          /\ \E w \in WriteRecs(k) :
               /\ w.start_ts = s
               /\ w.type = "write"
               /\ LET rc == [type |-> "resolve_committed", start_ts |-> s,
                             primary |-> k, commit_ts |-> w.ts]
                  IN /\ rc \notin msg_reqs
                     /\ msg_reqs' = msg_reqs \cup {rc}
          /\ UNCHANGED <<next_ts, client_vars, key_vars>>
       \/ \* already rolled back
          /\ ~HasOwnLock(k, s)
          /\ \E w \in WriteRecs(k) : w.start_ts = s /\ w.type = "rollback"
          /\ rb \notin msg_reqs
          /\ msg_reqs' = msg_reqs \cup {rb}
          /\ UNCHANGED <<next_ts, client_vars, key_vars>>
       \/ \* nothing found: write rollback record to block late prewrites
          /\ ~HasOwnLock(k, s)
          /\ ~HasRecord(k, s)
          /\ key_write' = [key_write EXCEPT ![k] = Append(@,
               [ts |-> s, start_ts |-> s, type |-> "rollback"])]
          /\ msg_reqs' = msg_reqs \cup {rb}
          /\ UNCHANGED <<next_ts, client_vars, key_lock, key_data>>

ServerResolveCommitted ==
  \E m \in msg_reqs :
    /\ m.type = "resolve_committed"
    /\ \E k \in KEY :
         /\ HasOwnLock(k, m.start_ts)
         /\ key_lock' = [key_lock EXCEPT ![k] = {}]
         /\ key_write' = [key_write EXCEPT ![k] = Append(@,
              [ts |-> m.commit_ts, start_ts |-> m.start_ts, type |-> "write"])]
    /\ UNCHANGED <<next_ts, client_vars, key_data, msg_reqs>>

ServerResolveRollbacked ==
  \E m \in msg_reqs :
    /\ m.type = "resolve_rollbacked"
    /\ \E k \in KEY :
         /\ HasOwnLock(k, m.start_ts)
         /\ key_lock' = [key_lock EXCEPT ![k] = {}]
         /\ key_write' = [key_write EXCEPT ![k] = Append(@,
              [ts |-> m.start_ts, start_ts |-> m.start_ts,
               type |-> "rollback"])]
    /\ UNCHANGED <<next_ts, client_vars, key_data, msg_reqs>>

-----------------------------------------------------------------------------
Terminated ==
  /\ \A c \in CLIENT : client_state[c] \in {"committed", "aborted"}
  /\ \A k \in KEY : key_lock[k] = {}
  /\ UNCHANGED vars

Next ==
  \/ \E c \in CLIENT :
       \/ ClientStartOptimistic(c)
       \/ ClientStartPessimistic(c)
       \/ ClientPrewritePessimistic(c)
       \/ ClientCommit(c)
  \/ ClientCheckTxnStatus
  \/ ServerLockKey
  \/ ServerPrewriteOptimistic
  \/ ServerPrewritePessimistic
  \/ ServerCommit
  \/ ServerCheckTxnStatus
  \/ ServerResolveCommitted
  \/ ServerResolveRollbacked
  \/ Terminated

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Safety properties

TypeOK ==
  /\ next_ts \in Nat
  /\ client_state \in [CLIENT -> ClientStates]
  /\ client_ts \in [CLIENT -> [start_ts : Nat, commit_ts : Nat,
                               for_update_ts : Nat]]
  /\ client_key \in [CLIENT -> [locking : SUBSET KEY,
                                prewriting : SUBSET KEY]]
  /\ \A k \in KEY : key_lock[k] \subseteq Locks
  /\ \A k \in KEY : key_write[k] \in Seq(Writes)
  /\ \A k \in KEY : key_data[k] \subseteq Nat
  /\ msg_reqs \subseteq ReqMessages

CommitConsistency ==
  \A c \in CLIENT :
    client_state[c] = "committed" =>
      LET rec == [ts |-> client_ts[c].commit_ts,
                  start_ts |-> client_ts[c].start_ts, type |-> "write"]
      IN /\ rec \in WriteRecs(CLIENT_PRIMARY[c])
         /\ \A k \in CLIENT_WRITE_KEY[c] :
              \/ rec \in WriteRecs(k)
              \/ \E l \in key_lock[k] :
                   l.ts = client_ts[c].start_ts /\ l.type # "lock_key"

AbortConsistency ==
  \A c \in CLIENT :
    client_state[c] = "aborted" =>
      \A k \in KEY : \A w \in WriteRecs(k) :
        ~(w.start_ts = client_ts[c].start_ts /\ w.type = "write")

WriteConsistency ==
  \A k \in KEY :
    /\ \A w \in WriteRecs(k) :
         /\ w.type = "write" => (w.ts > w.start_ts /\ w.start_ts \in key_data[k])
         /\ w.type = "rollback" => w.ts = w.start_ts
    /\ \A l \in key_lock[k] : l.type # "lock_key" => l.ts \in key_data[k]

UniqueLockOrWrite ==
  \A k \in KEY :
    /\ Cardinality(key_lock[k]) <= 1
    /\ \A l \in key_lock[k] : ~HasRecord(k, l.ts)

UniqueWrite ==
  \A k \in KEY :
    \A i, j \in DOMAIN key_write[k] :
      i # j =>
        /\ key_write[k][i].start_ts # key_write[k][j].start_ts
        /\ key_write[k][i].ts # key_write[k][j].ts

UniqueCommitOrAbort ==
  \A k1, k2 \in KEY :
    \A w1 \in WriteRecs(k1), w2 \in WriteRecs(k2) :
      w1.start_ts = w2.start_ts => w1.type = w2.type

MsgTsConsistency ==
  \A m \in msg_reqs :
    /\ m.start_ts > 0
    /\ m.start_ts < next_ts
    /\ m.type = "lock_key" =>
         (m.for_update_ts >= m.start_ts /\ m.for_update_ts < next_ts)
    /\ m.type \in {"commit", "resolve_committed"} =>
         (m.commit_ts > m.start_ts /\ m.commit_ts < next_ts)

\* No other transaction committed a write on our keys between our
\* snapshot (start_ts) and our commit_ts.
OptimisticReadSnapshotIsolation ==
  \A c \in OPTIMISTIC_CLIENT :
    client_state[c] = "committed" =>
      \A k \in CLIENT_WRITE_KEY[c] : \A w \in WriteRecs(k) :
        (w.type = "write" /\ w.start_ts # client_ts[c].start_ts) =>
          ~(w.ts > client_ts[c].start_ts /\ w.ts < client_ts[c].commit_ts)

\* For pessimistic transactions the snapshot is taken at for_update_ts.
PessimisticReadSnapshotIsolation ==
  \A c \in PESSIMISTIC_CLIENT :
    client_state[c] = "committed" =>
      \A k \in CLIENT_WRITE_KEY[c] : \A w \in WriteRecs(k) :
        (w.type = "write" /\ w.start_ts # client_ts[c].start_ts) =>
          ~(w.ts > client_ts[c].for_update_ts /\ w.ts < client_ts[c].commit_ts)

=============================================================================
```