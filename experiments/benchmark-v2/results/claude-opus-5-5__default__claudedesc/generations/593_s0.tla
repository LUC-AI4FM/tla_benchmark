                         k \in CLIENT_WRITE_KEY[c]})
  /\ UNCHANGED <<resp_msgs, key_vars, client_ts, client_read, next_ts>>

ClientPrewrited(c, k) ==
  /\ client_state[c] = "prewriting"
  /\ k \in client_key[c].prewriting
  /\ \E m \in resp_msgs :
       /\ m.type = "prewrited"
       /\ m.c = c
       /\ m.key = k
       /\ m.start_ts = client_ts[c].start_ts
  /\ client_key' = [client_key EXCEPT ![c].prewriting = @ \ {k}]
  /\ UNCHANGED <<req_msgs, resp_msgs, key_vars, client_state, client_ts,
                 client_read, next_ts>>

ClientCommit(c) ==
  /\ client_state[c] = "prewriting"
  /\ client_key[c].prewriting = {}
  /\ LET cts == next_ts IN
       /\ next_ts' = next_ts + 1
       /\ client_ts' = [client_ts EXCEPT ![c].commit_ts = cts]
       /\ client_state' = [client_state EXCEPT ![c] = "committing"]
       /\ SendReqs({[type |-> "commit", c |-> c, key |-> CLIENT_PRIMARY[c],
                     start_ts |-> client_ts[c].start_ts,
                     commit_ts |-> cts,
                     primary |-> CLIENT_PRIMARY[c]]})
  /\ UNCHANGED <<resp_msgs, key_vars, client_key, client_read>>

\* After the primary is committed, commit the secondary keys.
ClientCommitted(c) ==
  /\ client_state[c] = "committing"
  /\ \E m \in resp_msgs :
       /\ m.type = "committed"
       /\ m.start_ts = client_ts[c].start_ts
  /\ client_state' = [client_state EXCEPT ![c] = "committed"]
  /\ SendReqs({[type |-> "commit", c |-> c, key |-> k,
                start_ts |-> client_ts[c].start_ts,
                commit_ts |-> client_ts[c].commit_ts,
                primary |-> CLIENT_PRIMARY[c]] :
                 k \in CLIENT_WRITE_KEY[c] \ {CLIENT_PRIMARY[c]}})
  /\ UNCHANGED <<resp_msgs, key_vars, client_ts, client_key, client_read, next_ts>>

ClientAborted(c) ==
  /\ \/ /\ client_state[c] \in {"working", "prewriting"}
        /\ \E m \in resp_msgs :
             \/ /\ m.type \in {"lock_key_aborted", "prewrite_failed"}
                /\ m.c = c
                /\ m.start_ts = client_ts[c].start_ts
             \/ /\ m.type = "aborted"
                /\ m.start_ts = client_ts[c].start_ts
     \/ /\ client_state[c] = "committing"
        /\ \E m \in resp_msgs :
             /\ m.type = "aborted"
             /\ m.start_ts = client_ts[c].start_ts
  /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
  /\ UNCHANGED <<req_msgs, resp_msgs, key_vars, client_ts, client_key,
                 client_read, next_ts>>

-----------------------------------------------------------------------------
\* Server actions

ServerReadKey ==
  \E m \in req_msgs :
    /\ m.type = "get"
    /\ LET k  == m.key
           ts == m.start_ts
           idx == {i \in DOMAIN key_write[k] :
                     key_write[k][i].type = "write" /\ key_write[k][i].ts <= ts}
           val == IF idx = {} THEN 0
                  ELSE key_write[k][CHOOSE i \in idx :
                         \A j \in idx : key_write[k][i].ts >= key_write[k][j].ts].start_ts
       IN /\ ~\E l \in key_lock[k] : l.type # "lock_key" /\ l.ts <= ts
          /\ SendResp([type |-> "get_resp", c |-> m.c, key |-> k,
                       start_ts |-> ts, value |-> val])
    /\ UNCHANGED <<req_msgs, key_vars, client_vars, next_ts>>

ServerLockKey ==
  \E m \in req_msgs :
    /\ m.type = "lock_key"
    /\ LET k   == m.key
           ts  == m.start_ts
           fts == m.for_update_ts
       IN \/ /\ \E l \in key_lock[k] : l.ts = ts
             /\ SendResp([type |-> "lock_key_succeed", c |-> m.c, key |-> k,
                          start_ts |-> ts])
             /\ UNCHANGED key_vars
          \/ /\ key_lock[k] = {}
             /\ IF HasRollback(k, ts)
                THEN /\ SendResp([type |-> "lock_key_aborted", c |-> m.c,
                                  key |-> k, start_ts |-> ts])
                     /\ UNCHANGED key_vars
                ELSE IF LatestCommitTs(k) > fts
                THEN /\ SendResp([type |-> "lock_key_conflict", c |-> m.c,
                                  key |-> k, start_ts |-> ts,
                                  for_update_ts |-> fts,
                                  latest_commit_ts |-> LatestCommitTs(k)])
                     /\ UNCHANGED key_vars
                ELSE /\ key_lock' = [key_lock EXCEPT ![k] =
                                       {[ts |-> ts, primary |-> m.primary,
                                         type |-> "lock_key",
                                         for_update_ts |-> fts]}]
                     /\ SendResp([type |-> "lock_key_succeed", c |-> m.c,
                                  key |-> k, start_ts |-> ts])
                     /\ UNCHANGED <<key_data, key_write>>
    /\ UNCHANGED <<req_msgs, client_vars, next_ts>>

ServerPrewriteOptimistic ==
  \E m \in req_msgs :
    /\ m.type = "prewrite_optimistic"
    /\ LET k  == m.key
           ts == m.start_ts
       IN \/ /\ \E l \in key_lock[k] : l.ts = ts
             /\ SendResp([type |-> "prewrited", c |-> m.c, key |-> k,
                          start_ts |-> ts])
             /\ UNCHANGED key_vars
          \/ /\ key_lock[k] = {}
             /\ IF HasRollback(k, ts) \/ LatestCommitTs(k) >= ts
                THEN /\ SendResp([type |-> "prewrite_failed", c |-> m.c,
                                  key |-> k, start_ts |-> ts])
                     /\ UNCHANGED key_vars
                ELSE /\ key_lock' = [key_lock EXCEPT ![k] =
                                       {[ts |-> ts, primary |-> m.primary,
                                         type |-> "prewrite_optimistic",
                                         for_update_ts |-> 0]}]
                     /\ key_data' = [key_data EXCEPT ![k] = @ \cup {ts}]
                     /\ SendResp([type |-> "prewrited", c |-> m.c,
                                  key |-> k, start_ts |-> ts])
                     /\ UNCHANGED key_write
    /\ UNCHANGED <<req_msgs, client_vars, next_ts>>

ServerPrewritePessimistic ==
  \E m \in req_msgs :
    /\ m.type = "prewrite_pessimistic"
    /\ LET k  == m.key
           ts == m.start_ts
       IN \/ \E l \in key_lock[k] :
               /\ l.ts = ts
               /\ l.type = "lock_key"
               /\ key_lock' = [key_lock EXCEPT ![k] =
                                 {[l EXCEPT !.type = "prewrite_pessimistic"]}]
               /\ key_data' = [key_data EXCEPT ![k] = @ \cup {ts}]
               /\ SendResp([type |-> "prewrited", c |-> m.c, key |-> k,
                            start_ts |-> ts])
               /\ UNCHANGED key_write
          \/ /\ \E l \in key_lock[k] : l.ts = ts /\ l.type = "prewrite_pessimistic"
             /\ SendResp([type |-> "prewrited", c |-> m.c, key |-> k,
                          start_ts |-> ts])
             /\ UNCHANGED key_vars
          \/ /\ ~\E l \in key_lock[k] : l.ts = ts
             /\ SendResp([type |-> "prewrite_failed", c |-> m.c, key |-> k,
                          start_ts |-> ts])
             /\ UNCHANGED key_vars
    /\ UNCHANGED <<req_msgs, client_vars, next_ts>>

ServerCommitPrimary ==
  \E m \in req_msgs :
    /\ m.type = "commit"
    /\ m.key = m.primary
    /\ LET k   == m.key
           ts  == m.start_ts
           cts == m.commit_ts
           prewritten == \E l \in key_lock[k] : l.ts = ts /\ l.type # "lock_key"
       IN \/ /\ prewritten
             /\ key_lock' = [key_lock EXCEPT ![k] = {}]
             /\ key_write' = [key_write EXCEPT ![k] =
                                Append(@, [ts |-> cts, start_ts |-> ts,
                                           type |-> "write"])]
             /\ SendResp([type |-> "committed", start_ts |-> ts, commit_ts |-> cts])
             /\ UNCHANGED key_data
          \/ /\ ~prewritten
             /\ CommitRecIdx(k, ts) # {}
             /\ SendResp([type |-> "committed", start_ts |-> ts,
                          commit_ts |-> key_write[k][CHOOSE i \in CommitRecIdx(k, ts) : TRUE].ts])
             /\ UNCHANGED key_vars
          \/ /\ ~prewritten
             /\ CommitRecIdx(k, ts) = {}
             /\ key_lock' = [key_lock EXCEPT ![k] = {l \in @ : l.ts # ts}]
             /\ key_write' = IF HasRollback(k, ts) THEN key_write
                             ELSE [key_write EXCEPT ![k] =
                                     Append(@, [ts |-> ts, start_ts |-> ts,
                                                type |-> "rollback"])]
             /\ SendResp([type |-> "aborted", start_ts |-> ts])
             /\ UNCHANGED key_data
    /\ UNCHANGED <<req_msgs, client_vars, next_ts>>

ServerCommitSecondary ==
  \E m \in req_msgs :
    /\ m.type = "commit"
    /\ m.key # m.primary
    /\ \E l \in key_lock[m.key] : l.ts = m.start_ts
    /\ key_lock' = [key_lock EXCEPT ![m.key] = {}]
    /\ key_write' = [key_write EXCEPT ![m.key] =
                       Append(@, [ts |-> m.commit_ts, start_ts |-> m.start_ts,
                                  type |-> "write"])]
    /\ UNCHANGED <<req_msgs, resp_msgs, key_data, client_vars, next_ts>>

\* check_txn_status: resolve a (possibly stale) lock left by another transaction.
ServerCheckTxnStatus(k) ==
  \E l \in key_lock[k] :
    LET p  == l.primary
        ts == l.ts
        committed == CommitRecIdx(p, ts)
    IN \/ /\ committed # {}
          /\ key_lock' = [key_lock EXCEPT ![k] = {}]
          /\ key_write' = [key_write EXCEPT ![k] =
                             Append(@, [ts |-> key_write[p][CHOOSE i \in committed : TRUE].ts,
                                        start_ts |-> ts, type |-> "write"])]
          /\ UNCHANGED resp_msgs
       \/ /\ committed = {}
          /\ HasRollback(p, ts)
          /\ key_lock' = [key_lock EXCEPT ![k] = {}]
          /\ key_write' = IF HasRollback(k, ts) THEN key_write
                          ELSE [key_write EXCEPT ![k] =
                                  Append(@, [ts |-> ts, start_ts |-> ts,
                                             type |-> "rollback"])]
          /\ UNCHANGED resp_msgs
       \/ /\ committed = {}
          /\ ~HasRollback(p, ts)
          /\ key_lock' = [key_lock EXCEPT ![p] = {x \in @ : x.ts # ts}]
          /\ key_write' = [key_write EXCEPT ![p] =
                             Append(@, [ts |-> ts, start_ts |-> ts,
                                        type |-> "rollback"])]
          /\ SendResp([type |-> "aborted", start_ts |-> ts])
    /\ UNCHANGED <<req_msgs, key_data, client_vars, next_ts>>

-----------------------------------------------------------------------------
Next ==
  \/ \E c \in CLIENT :
       \/ ClientStart(c)
       \/ ClientRetryLockKey(c)
       \/ ClientPrewrite(c)
       \/ ClientCommit(c)
       \/ ClientCommitted(c)
       \/ ClientAborted(c)
       \/ \E k \in KEY :
            \/ ClientReadValue(c, k)
            \/ ClientLockedKey(c, k)
            \/ ClientPrewrited(c, k)
  \/ ServerReadKey
  \/ ServerLockKey
  \/ ServerPrewriteOptimistic
  \/ ServerPrewritePessimistic
  \/ ServerCommitPrimary
  \/ ServerCommitSecondary
  \/ \E k \in KEY : ServerCheckTxnStatus(k)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Safety properties

TypeOK ==
  /\ req_msgs \subseteq ReqMessages
  /\ resp_msgs \subseteq RespMessages
  /\ key_data \in [KEY -> SUBSET Nat]
  /\ key_lock \in [KEY -> SUBSET Lock]
  /\ \A k \in KEY : Cardinality(key_lock[k]) <= 1
  /\ key_write \in [KEY -> Seq(Write)]
  /\ client_state \in [CLIENT -> ClientStage]
  /\ client_ts \in [CLIENT -> [start_ts : Nat, commit_ts : Nat, for_update_ts : Nat]]
  /\ client_key \in [CLIENT -> [reading : SUBSET KEY, locking : SUBSET KEY,
                                prewriting : SUBSET KEY]]
  /\ client_read \in [CLIENT -> [KEY -> Nat \cup {NoValue}]]
  /\ next_ts \in Nat \ {0}

CommittedTxns == {m.start_ts : m \in {x \in resp_msgs : x.type = "committed"}}
AbortedTxns   == {m.start_ts : m \in {x \in resp_msgs : x.type = "aborted"}}

\* No transaction is both committed and aborted.
CommitAbortConsistency == CommittedTxns \cap AbortedTxns = {}

\* A key never holds both a commit and a rollback record for the same transaction.
WriteConsistency ==
  \A k \in KEY : \A i, j \in DOMAIN key_write[k] :
     key_write[k][i].start_ts = key_write[k][j].start_ts =>
        key_write[k][i].type = key_write[k][j].type

\* Each transaction has a unique commit timestamp.
UniqueCommitTs ==
  \A m1, m2 \in {x \in resp_msgs : x.type = "committed"} :
     m1.start_ts = m2.start_ts => m1.commit_ts = m2.commit_ts

THEOREM Spec => [](TypeOK /\ CommitAbortConsistency /\ WriteConsistency /\ UniqueCommitTs)
=============================================================================