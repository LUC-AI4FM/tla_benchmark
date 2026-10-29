```tla
]) : k \in CLIENT_WRITE_KEY[c]}
  /\ UNCHANGED <<resp_msgs, key_data, key_lock, key_write, client_ts, next_ts>>

ClientPessimisticBegin(c) ==
  /\ c \in PESSIMISTIC_CLIENT
  /\ client_stage[c] = "init"
  /\ next_ts' = next_ts + 2
  /\ client_ts' = [client_ts EXCEPT ![c].start_ts = next_ts + 1,
                                    ![c].for_update_ts = next_ts + 2]
  /\ client_stage' = [client_stage EXCEPT ![c] = "locking"]
  /\ req_msgs' = req_msgs \cup
       {MkReq("lock_key", next_ts + 1, next_ts + 2, k, CLIENT_PRIMARY[c]) : k \in CLIENT_WRITE_KEY[c]}
  /\ UNCHANGED <<resp_msgs, key_data, key_lock, key_write, client_read>>

ClientLockDone(c) ==
  /\ client_stage[c] = "locking"
  /\ LET s == client_ts[c].start_ts IN
     /\ \A k \in CLIENT_WRITE_KEY[c] : HasResp("lock_key_resp", s, k)
     /\ client_read' = [client_read EXCEPT ![c] =
          [k \in KEY |-> IF k \in CLIENT_WRITE_KEY[c]
                         THEN (CHOOSE m \in resp_msgs : m.type = "lock_key_resp"
                                  /\ m.start_ts = s /\ m.key = k).value
                         ELSE NoValue]]
     /\ client_stage' = [client_stage EXCEPT ![c] = "prewriting"]
     /\ req_msgs' = req_msgs \cup
          {MkReq("prewrite_pessimistic", s, s, k, CLIENT_PRIMARY[c]) : k \in CLIENT_WRITE_KEY[c]}
  /\ UNCHANGED <<resp_msgs, key_data, key_lock, key_write, client_ts, next_ts>>

ClientLockFailed(c) ==
  /\ client_stage[c] = "locking"
  /\ HasRespAny("lock_failed", client_ts[c].start_ts)
  /\ client_stage' = [client_stage EXCEPT ![c] = "aborted"]
  /\ UNCHANGED <<req_msgs, resp_msgs, key_data, key_lock, key_write, client_ts, client_read, next_ts>>

ClientPrewriteDone(c) ==
  /\ client_stage[c] = "prewriting"
  /\ LET s == client_ts[c].start_ts IN
     /\ \A k \in CLIENT_WRITE_KEY[c] : HasResp("prewrited", s, k)
     /\ next_ts' = next_ts + 1
     /\ client_ts' = [client_ts EXCEPT ![c].commit_ts = next_ts + 1]
     /\ client_stage' = [client_stage EXCEPT ![c] = "committing"]
     /\ req_msgs' = req_msgs \cup
          {MkReq("commit", s, next_ts + 1, CLIENT_PRIMARY[c], CLIENT_PRIMARY[c])}
  /\ UNCHANGED <<resp_msgs, key_data, key_lock, key_write, client_read>>

ClientPrewriteFailed(c) ==
  /\ client_stage[c] = "prewriting"
  /\ HasRespAny("prewrite_aborted", client_ts[c].start_ts)
  /\ client_stage' = [client_stage EXCEPT ![c] = "aborted"]
  /\ UNCHANGED <<req_msgs, resp_msgs, key_data, key_lock, key_write, client_ts, client_read, next_ts>>

ClientCommitPrimaryDone(c) ==
  /\ client_stage[c] = "committing"
  /\ LET s == client_ts[c].start_ts IN
     /\ HasResp("committed", s, CLIENT_PRIMARY[c])
     /\ client_stage' = [client_stage EXCEPT ![c] = "committed"]
     /\ req_msgs' = req_msgs \cup
          {MkReq("commit", s, client_ts[c].commit_ts, k, CLIENT_PRIMARY[c]) :
             k \in CLIENT_WRITE_KEY[c] \ {CLIENT_PRIMARY[c]}}
  /\ UNCHANGED <<resp_msgs, key_data, key_lock, key_write, client_ts, client_read, next_ts>>

ClientCommitFailed(c) ==
  /\ client_stage[c] = "committing"
  /\ HasRespAny("commit_aborted", client_ts[c].start_ts)
  /\ client_stage' = [client_stage EXCEPT ![c] = "aborted"]
  /\ UNCHANGED <<req_msgs, resp_msgs, key_data, key_lock, key_write, client_ts, client_read, next_ts>>

-----------------------------------------------------------------------------
\* Server actions

ServerGet(m) ==
  /\ m.type = "get"
  /\ ~\E l \in key_lock[m.key] : l.type \in PrewriteLockTypes /\ l.ts <= m.start_ts
  /\ req_msgs' = req_msgs \ {m}
  /\ resp_msgs' = resp_msgs \cup
       {MkResp("get_resp", m.start_ts, m.start_ts, m.key, LatestVersion(m.key, m.start_ts))}
  /\ UNCHANGED <<key_data, key_lock, key_write, client_stage, client_ts, client_read, next_ts>>

LockConflict(m) ==
  \/ HasRollback(m.key, m.start_ts)
  \/ \E w \in key_write[m.key] : w.type = "write" /\ w.ts > m.ts

ServerLockKeyFail(m) ==
  /\ m.type = "lock_key"
  /\ LockConflict(m)
  /\ req_msgs' = req_msgs \ {m}
  /\ resp_msgs' = resp_msgs \cup {MkResp("lock_failed", m.start_ts, m.ts, m.key, NoValue)}
  /\ UNCHANGED <<key_data, key_lock, key_write, client_stage, client_ts, client_read, next_ts>>

ServerLockKey(m) ==
  /\ m.type = "lock_key"
  /\ ~LockConflict(m)
  /\ key_lock[m.key] = {}
  /\ key_lock' = [key_lock EXCEPT ![m.key] =
       {[ts |-> m.start_ts, primary |-> m.primary, type |-> "lock_key", for_update_ts |-> m.ts]}]
  /\ req_msgs' = req_msgs \ {m}
  /\ resp_msgs' = resp_msgs \cup
       {MkResp("lock_key_resp", m.start_ts, m.ts, m.key, LatestVersion(m.key, m.ts))}
  /\ UNCHANGED <<key_data, key_write, client_stage, client_ts, client_read, next_ts>>

PrewriteConflict(m) ==
  \/ HasRollback(m.key, m.start_ts)
  \/ \E w \in key_write[m.key] : w.type = "write" /\ w.ts > m.start_ts

ServerPrewriteOptimisticFail(m) ==
  /\ m.type = "prewrite_optimistic"
  /\ PrewriteConflict(m)
  /\ req_msgs' = req_msgs \ {m}
  /\ resp_msgs' = resp_msgs \cup {MkResp("prewrite_aborted", m.start_ts, m.ts, m.key, NoValue)}
  /\ UNCHANGED <<key_data, key_lock, key_write, client_stage, client_ts, client_read, next_ts>>

ServerPrewriteOptimistic(m) ==
  /\ m.type = "prewrite_optimistic"
  /\ ~PrewriteConflict(m)
  /\ key_lock[m.key] = {}
  /\ key_lock' = [key_lock EXCEPT ![m.key] =
       {[ts |-> m.start_ts, primary |-> m.primary, type |-> "prewrite_optimistic", for_update_ts |-> 0]}]
  /\ key_data' = [key_data EXCEPT ![m.key] = @ \cup {m.start_ts}]
  /\ req_msgs' = req_msgs \ {m}
  /\ resp_msgs' = resp_msgs \cup {MkResp("prewrited", m.start_ts, m.ts, m.key, NoValue)}
  /\ UNCHANGED <<key_write, client_stage, client_ts, client_read, next_ts>>

ServerPrewritePessimistic(m) ==
  /\ m.type = "prewrite_pessimistic"
  /\ req_msgs' = req_msgs \ {m}
  /\ IF \E l \in key_lock[m.key] : l.ts = m.start_ts /\ l.type = "lock_key"
     THEN LET l == CHOOSE x \in key_lock[m.key] : x.ts = m.start_ts /\ x.type = "lock_key"
          IN /\ key_lock' = [key_lock EXCEPT ![m.key] =
                  {[ts |-> l.ts, primary |-> l.primary, type |-> "prewrite_pessimistic",
                    for_update_ts |-> l.for_update_ts]}]
             /\ key_data' = [key_data EXCEPT ![m.key] = @ \cup {m.start_ts}]
             /\ resp_msgs' = resp_msgs \cup {MkResp("prewrited", m.start_ts, m.ts, m.key, NoValue)}
     ELSE /\ resp_msgs' = resp_msgs \cup
               {MkResp("prewrite_aborted", m.start_ts, m.ts, m.key, NoValue)}
          /\ UNCHANGED <<key_lock, key_data>>
  /\ UNCHANGED <<key_write, client_stage, client_ts, client_read, next_ts>>

ServerCommit(m) ==
  /\ m.type = "commit"
  /\ req_msgs' = req_msgs \ {m}
  /\ IF HasCommit(m.key, m.start_ts)
     THEN /\ resp_msgs' = resp_msgs \cup {MkResp("committed", m.start_ts, m.ts, m.key, NoValue)}
          /\ UNCHANGED <<key_lock, key_write>>
     ELSE IF \E l \in key_lock[m.key] : l.ts = m.start_ts /\ l.type \in PrewriteLockTypes
     THEN /\ key_lock' = [key_lock EXCEPT ![m.key] = {x \in @ : x.ts /= m.start_ts}]
          /\ key_write' = [key_write EXCEPT ![m.key] =
               @ \cup {[ts |-> m.ts, start_ts |-> m.start_ts, type |-> "write"]}]
          /\ resp_msgs' = resp_msgs \cup {MkResp("committed", m.start_ts, m.ts, m.key, NoValue)}
     ELSE /\ resp_msgs' = resp_msgs \cup
               {MkResp("commit_aborted", m.start_ts, m.ts, m.key, NoValue)}
          /\ UNCHANGED <<key_lock, key_write>>
  /\ UNCHANGED <<key_data, client_stage, client_ts, client_read, next_ts>>

\* check_txn_status: resolve a (possibly stale) lock on key k by consulting its primary.
ServerCheckTxnStatus(k) ==
  \E l \in key_lock[k] :
    LET p == l.primary
        s == l.ts
    IN /\ IF HasCommit(p, s)
          THEN LET w == CHOOSE x \in key_write[p] : x.type = "write" /\ x.start_ts = s
               IN /\ l.type \in PrewriteLockTypes
                  /\ key_lock' = [key_lock EXCEPT ![k] = @ \ {l}]
                  /\ key_write' = [key_write EXCEPT ![k] =
                       @ \cup {[ts |-> w.ts, start_ts |-> s, type |-> "write"]}]
          ELSE /\ key_lock' = [kk \in KEY |->
                    IF kk \in {p, k} THEN {x \in key_lock[kk] : x.ts /= s}
                    ELSE key_lock[kk]]
               /\ key_write' = [kk \in KEY |->
                    IF kk \in {p, k} /\ ~HasRollback(kk, s)
                    THEN key_write[kk] \cup {[ts |-> s, start_ts |-> s, type |-> "rollback"]}
                    ELSE key_write[kk]]
       /\ UNCHANGED <<req_msgs, resp_msgs, key_data, client_stage, client_ts, client_read, next_ts>>

AllDone ==
  /\ \A c \in CLIENT : client_stage[c] \in {"committed", "aborted"}
  /\ UNCHANGED vars

-----------------------------------------------------------------------------
Next ==
  \/ \E c \in CLIENT :
       \/ ClientOptimisticBegin(c)
       \/ ClientReadDone(c)
       \/ ClientPessimisticBegin(c)
       \/ ClientLockDone(c)
       \/ ClientLockFailed(c)
       \/ ClientPrewriteDone(c)
       \/ ClientPrewriteFailed(c)
       \/ ClientCommitPrimaryDone(c)
       \/ ClientCommitFailed(c)
  \/ \E m \in req_msgs :
       \/ ServerGet(m)
       \/ ServerLockKeyFail(m)
       \/ ServerLockKey(m)
       \/ ServerPrewriteOptimisticFail(m)
       \/ ServerPrewriteOptimistic(m)
       \/ ServerPrewritePessimistic(m)
       \/ ServerCommit(m)
  \/ \E k \in KEY : ServerCheckTxnStatus(k)
  \/ AllDone

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Safety properties

CommittedTxn == {m.start_ts : m \in {x \in resp_msgs : x.type = "committed"}}
AbortedTxn == {m.start_ts : m \in {x \in resp_msgs :
                 x.type \in {"lock_failed", "prewrite_aborted", "commit_aborted"}}}

UniqueCommitOrAbort == CommittedTxn \cap AbortedTxn = {}

UniqueLockOrWrite ==
  \A k \in KEY : \A l \in key_lock[k] : ~HasWrite(k, l.ts)

UniqueWrite ==
  \A k \in KEY : \A w1, w2 \in key_write[k] :
    /\ (w1.start_ts = w2.start_ts => w1 = w2)
    /\ (w1.ts = w2.ts => w1 = w2)

WriteConsistency ==
  \A k \in KEY : \A w \in key_write[k] :
    w.type = "write" => (w.start_ts \in key_data[k] /\ w.ts > w.start_ts)

CommitConsistency ==
  \A c \in CLIENT : client_stage[c] = "committed" =>
    /\ HasCommit(CLIENT_PRIMARY[c], client_ts[c].start_ts)
    /\ \A k \in CLIENT_WRITE_KEY[c] :
         \/ \E w \in key_write[k] : w.type = "write" /\ w.start_ts = client_ts[c].start_ts
                                    /\ w.ts = client_ts[c].commit_ts
         \/ \E l \in key_lock[k] : l.ts = client_ts[c].start_ts

AbortConsistency ==
  \A c \in CLIENT : client_stage[c] = "aborted" =>
    ~HasCommit(CLIENT_PRIMARY[c], client_ts[c].start_ts)

MsgTsConsistency ==
  /\ \A m \in req_msgs : m.start_ts <= next_ts /\ m.ts <= next_ts
  /\ \A m \in resp_msgs : m.start_ts <= next_ts /\ m.ts <= next_ts /\ m.value <= next_ts

OptimisticReadSnapshotIsolation ==
  \A m \in resp_msgs : m.type = "get_resp" =>
    m.value = LatestVersion(m.key, m.start_ts)

PessimisticReadSnapshotIsolation ==
  \A m \in resp_msgs : m.type = "lock_key_resp" =>
    m.value = LatestVersion(m.key, m.ts)

=============================================================================
```