```tla
 = [c \in CLIENT |-> [k \in KEY |-> NoRead]]
  /\ key_lock = [k \in KEY |-> {}]
  /\ key_write = [k \in KEY |-> <<>>]
  /\ req_msgs = {}
  /\ resp_msgs = {}

-----------------------------------------------------------------------------
(* Client actions *)

ClientStart(c) ==
  /\ client_state[c] = "init"
  /\ client_ts' = [client_ts EXCEPT ![c] =
        [start_ts |-> next_ts, commit_ts |-> 0, for_update_ts |-> next_ts]]
  /\ next_ts' = next_ts + 1
  /\ client_state' = [client_state EXCEPT ![c] = "working"]
  /\ UNCHANGED <<client_key, client_read, key_lock, key_write, req_msgs, resp_msgs>>

ClientReadOptimistic(c, k) ==
  /\ c \in OPTIMISTIC_CLIENT
  /\ client_state[c] = "working"
  /\ k \in CLIENT_READ_KEY[c]
  /\ ~client_read[c][k].done
  /\ ~\E l \in key_lock[k] : l.ts <= StartTs(c)
  /\ client_read' = [client_read EXCEPT ![c][k] =
        [done |-> TRUE, ts |-> StartTs(c), val |-> SnapshotValue(k, StartTs(c))]]
  /\ UNCHANGED <<next_ts, client_state, client_ts, client_key,
                 key_lock, key_write, req_msgs, resp_msgs>>

ClientPrewriteOptimistic(c) ==
  /\ c \in OPTIMISTIC_CLIENT
  /\ client_state[c] = "working"
  /\ \A k \in CLIENT_READ_KEY[c] : client_read[c][k].done
  /\ SendReqs({Msg("prewrite_optimistic", c, k, StartTs(c), 0, 0, 0)
                 : k \in CLIENT_WRITE_KEY[c]})
  /\ client_state' = [client_state EXCEPT ![c] = "prewriting"]
  /\ UNCHANGED <<next_ts, client_ts, client_key, client_read,
                 key_lock, key_write, resp_msgs>>

ClientLockKey(c) ==
  /\ c \in PESSIMISTIC_CLIENT
  /\ client_state[c] = "working"
  /\ SendReqs({Msg("lock_key", c, k, StartTs(c), client_ts[c].for_update_ts, 0, 0)
                 : k \in CLIENT_WRITE_KEY[c]})
  /\ client_state' = [client_state EXCEPT ![c] = "locking"]
  /\ UNCHANGED <<next_ts, client_ts, client_key, client_read,
                 key_lock, key_write, resp_msgs>>

ClientRetryLockKey(c) ==
  /\ c \in PESSIMISTIC_CLIENT
  /\ client_state[c] = "locking"
  /\ next_ts < MAX_TS
  /\ \E r \in resp_msgs :
       /\ r.type = "lock_key_conflict" /\ r.c = c
       /\ r.start_ts = StartTs(c)
       /\ r.for_update_ts = client_ts[c].for_update_ts
       /\ r.key \notin client_key[c].locked
  /\ client_ts' = [client_ts EXCEPT ![c].for_update_ts = next_ts]
  /\ next_ts' = next_ts + 1
  /\ SendReqs({Msg("lock_key", c, k, StartTs(c), next_ts, 0, 0)
                 : k \in CLIENT_WRITE_KEY[c] \ client_key[c].locked})
  /\ UNCHANGED <<client_state, client_key, client_read, key_lock, key_write, resp_msgs>>

ClientLockedKey(c) ==
  /\ client_state[c] = "locking"
  /\ \E r \in resp_msgs :
       /\ r.type = "locked_key" /\ r.c = c
       /\ r.start_ts = StartTs(c)
       /\ r.key \notin client_key[c].locked
       /\ client_key' = [client_key EXCEPT ![c].locked = @ \cup {r.key}]
       /\ client_read' = IF r.key \in CLIENT_READ_KEY[c]
                         THEN [client_read EXCEPT ![c][r.key] =
                                 [done |-> TRUE, ts |-> r.for_update_ts, val |-> r.val]]
                         ELSE client_read
  /\ UNCHANGED <<next_ts, client_state, client_ts, key_lock, key_write,
                 req_msgs, resp_msgs>>

ClientPrewritePessimistic(c) ==
  /\ c \in PESSIMISTIC_CLIENT
  /\ client_state[c] = "locking"
  /\ client_key[c].locked = CLIENT_WRITE_KEY[c]
  /\ SendReqs({Msg("prewrite_pessimistic", c, k, StartTs(c), 0, 0, 0)
                 : k \in CLIENT_WRITE_KEY[c]})
  /\ client_state' = [client_state EXCEPT ![c] = "prewriting"]
  /\ UNCHANGED <<next_ts, client_ts, client_key, client_read,
                 key_lock, key_write, resp_msgs>>

ClientPrewrited(c) ==
  /\ client_state[c] = "prewriting"
  /\ \E r \in resp_msgs :
       /\ r.type = "prewrited" /\ r.c = c
       /\ r.start_ts = StartTs(c)
       /\ r.key \notin client_key[c].prewrited
       /\ client_key' = [client_key EXCEPT ![c].prewrited = @ \cup {r.key}]
  /\ UNCHANGED <<next_ts, client_state, client_ts, client_read, key_lock,
                 key_write, req_msgs, resp_msgs>>

ClientCommit(c) ==
  /\ client_state[c] = "prewriting"
  /\ client_key[c].prewrited = CLIENT_WRITE_KEY[c]
  /\ client_ts' = [client_ts EXCEPT ![c].commit_ts = next_ts]
  /\ next_ts' = next_ts + 1
  /\ SendReqs({Msg("commit", c, CLIENT_PRIMARY[c], StartTs(c), 0, next_ts, 0)})
  /\ client_state' = [client_state EXCEPT ![c] = "committing"]
  /\ UNCHANGED <<client_key, client_read, key_lock, key_write, resp_msgs>>

ClientCommitted(c) ==
  /\ client_state[c] = "committing"
  /\ \E r \in resp_msgs :
       r.type = "committed" /\ r.c = c /\ r.start_ts = StartTs(c)
  /\ client_state' = [client_state EXCEPT ![c] = "committed"]
  /\ UNCHANGED <<next_ts, client_ts, client_key, client_read, key_lock,
                 key_write, req_msgs, resp_msgs>>

ClientAbort(c) ==
  /\ client_state[c] \in {"locking", "prewriting", "committing"}
  /\ \E r \in resp_msgs :
       /\ r.type \in {"lock_failed", "prewrite_aborted", "commit_aborted"}
       /\ r.c = c /\ r.start_ts = StartTs(c)
  /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
  /\ UNCHANGED <<next_ts, client_ts, client_key, client_read, key_lock,
                 key_write, req_msgs, resp_msgs>>

-----------------------------------------------------------------------------
(* Server actions *)

ServerLockKey ==
  \E m \in req_msgs :
    /\ m.type = "lock_key"
    /\ LET k == m.key
           s == m.start_ts
       IN IF Records(k, s) # {} THEN
            /\ \E w \in Records(k, s) : w.type = "rollback"
            /\ SendResp(Msg("lock_failed", m.c, k, s, 0, 0, 0))
            /\ UNCHANGED <<key_lock, key_write>>
          ELSE IF OwnLock(k, s) # {} THEN
            LET l == CHOOSE l \in OwnLock(k, s) : TRUE
            IN /\ SendResp(Msg("locked_key", m.c, k, s, l.for_update_ts, 0,
                               SnapshotValue(k, l.for_update_ts)))
               /\ UNCHANGED <<key_lock, key_write>>
          ELSE IF key_lock[k] # {} THEN FALSE
          ELSE IF \E w \in Range(key_write[k]) :
                    w.type = "write" /\ w.ts > m.for_update_ts THEN
            /\ SendResp(Msg("lock_key_conflict", m.c, k, s, m.for_update_ts, 0, 0))
            /\ UNCHANGED <<key_lock, key_write>>
          ELSE
            /\ key_lock' = [key_lock EXCEPT ![k] =
                 {[ts |-> s, primary |-> CLIENT_PRIMARY[m.c], type |-> "lock_key",
                   for_update_ts |-> m.for_update_ts]}]
            /\ resp_msgs' = resp_msgs \cup
                 {Msg("locked_key", m.c, k, s, m.for_update_ts, 0,
                      SnapshotValue(k, m.for_update_ts))}
            /\ UNCHANGED key_write
    /\ UNCHANGED <<next_ts, client_state, client_ts, client_key, client_read, req_msgs>>

ServerPrewriteOptimistic ==
  \E m \in req_msgs :
    /\ m.type = "prewrite_optimistic"
    /\ LET k == m.key
           s == m.start_ts
       IN IF Records(k, s) # {} THEN
            /\ \E w \in Records(k, s) : w.type = "rollback"
            /\ SendResp(Msg("prewrite_aborted", m.c, k, s, 0, 0, 0))
            /\ UNCHANGED <<key_lock, key_write>>
          ELSE IF OwnLock(k, s) # {} THEN
            /\ SendResp(Msg("prewrited", m.c, k, s, 0, 0, 0))
            /\ UNCHANGED <<key_lock, key_write>>
          ELSE IF key_lock[k] # {} THEN FALSE
          ELSE IF \E w \in Range(key_write[k]) : w.type = "write" /\ w.ts >= s THEN
            /\ SendResp(Msg("prewrite_aborted", m.c, k, s, 0, 0, 0))
            /\ UNCHANGED <<key_lock, key_write>>
          ELSE
            /\ key_lock' = [key_lock EXCEPT ![k] =
                 {[ts |-> s, primary |-> CLIENT_PRIMARY[m.c],
                   type |-> "prewrite_optimistic", for_update_ts |-> 0]}]
            /\ resp_msgs' = resp_msgs \cup {Msg("prewrited", m.c, k, s, 0, 0, 0)}
            /\ UNCHANGED key_write
    /\ UNCHANGED <<next_ts, client_state, client_ts, client_key, client_read, req_msgs>>

ServerPrewritePessimistic ==
  \E m \in req_msgs :
    /\ m.type = "prewrite_pessimistic"
    /\ LET k == m.key
           s == m.start_ts
       IN IF Records(k, s) # {} THEN
            /\ \E w \in Records(k, s) : w.type = "rollback"
            /\ SendResp(Msg("prewrite_aborted", m.c, k, s, 0, 0, 0))
            /\ UNCHANGED <<key_lock, key_write>>
          ELSE IF OwnLock(k, s) # {} THEN
            LET l == CHOOSE l \in OwnLock(k, s) : TRUE
            IN IF l.type = "lock_key" THEN
                 /\ key_lock' = [key_lock EXCEPT ![k] =
                      {[l EXCEPT !.type = "prewrite_pessimistic"]}]
                 /\ resp_msgs' = resp_msgs \cup {Msg("prewrited", m.c, k, s, 0, 0, 0)}
                 /\ UNCHANGED key_write
               ELSE
                 /\ SendResp(Msg("prewrited", m.c, k, s, 0, 0, 0))
                 /\ UNCHANGED <<key_lock, key_write>>
          ELSE
            /\ SendResp(Msg("prewrite_aborted", m.c, k, s, 0, 0, 0))
            /\ UNCHANGED <<key_lock, key_write>>
    /\ UNCHANGED <<next_ts, client_state, client_ts, client_key, client_read, req_msgs>>

ServerCommit ==
  \E m \in req_msgs :
    /\ m.type = "commit"
    /\ LET k == m.key
           s == m.start_ts
       IN IF \E w \in Records(k, s) : w.type = "write" THEN
            /\ SendResp(Msg("committed", m.c, k, s, 0, m.commit_ts, 0))
            /\ UNCHANGED <<key_lock, key_write>>
          ELSE IF Records(k, s) # {} THEN
            /\ SendResp(Msg("commit_aborted", m.c, k, s, 0, 0, 0))
            /\ UNCHANGED <<key_lock, key_write>>
          ELSE IF \E l \in OwnLock(k, s) : l.type # "lock_key" THEN
            /\ key_lock' = [key_lock EXCEPT ![k] = {}]
            /\ key_write' = [key_write EXCEPT ![k] =
                 Append(@, [ts |-> m.commit_ts, start_ts |-> s, type |-> "write"])]
            /\ resp_msgs' = resp_msgs \cup
                 {Msg("committed", m.c, k, s, 0, m.commit_ts, 0)}
          ELSE
            /\ SendResp(Msg("commit_aborted", m.c, k, s, 0, 0, 0))
            /\ UNCHANGED <<key_lock, key_write>>
    /\ UNCHANGED <<next_ts, client_state, client_ts, client_key, client_read, req_msgs>>

\* Resolve a (possibly stale) lock by consulting its primary: roll forward if the
\* primary committed, otherwise roll back both the lock and the primary.
ServerResolveLock(k) ==
  /\ \E l \in key_lock[k] :
       LET p   == l.primary
           s   == l.ts
           cws == {w \in Records(p, s) : w.type = "write"}
       IN IF cws # {} THEN
            /\ key_lock' = [key_lock EXCEPT ![k] = {}]
            /\ key_write' = [key_write EXCEPT ![k] =
                 Append(@, [ts |-> (CHOOSE w \in cws : TRUE).ts,
                            start_ts |-> s, type |-> "write"])]
          ELSE
            /\ key_lock' = [kk \in KEY |->
                 IF kk \in {k, p} THEN key_lock[kk] \ OwnLock(kk, s)
                 ELSE key_lock[kk]]
            /\ key_write' = [kk \in KEY |->
                 IF kk \in {k, p} /\ Records(kk, s) = {}
                 THEN Append(key_write[kk],
                             [ts |-> s, start_ts |-> s, type |-> "rollback"])
                 ELSE key_write[kk]]
  /\ UNCHANGED <<next_ts, client_state, client_ts, client_key, client_read,
                 req_msgs, resp_msgs>>

Terminated ==
  /\ \A c \in CLIENT : client_state[c] \in {"committed", "aborted"}
  /\ \A k \in KEY : key_lock[k] = {}
  /\ UNCHANGED vars

-----------------------------------------------------------------------------
Next ==
  \/ \E c \in CLIENT :
       \/ ClientStart(c)
       \/ \E k \in KEY : ClientReadOptimistic(c, k)
       \/ ClientPrewriteOptimistic(c)
       \/ ClientLockKey(c)
       \/ ClientRetryLockKey(c)
       \/ ClientLockedKey(c)
       \/ ClientPrewritePessimistic(c)
       \/ ClientPrewrited(c)
       \/ ClientCommit(c)
       \/ ClientCommitted(c)
       \/ ClientAbort(c)
  \/ ServerLockKey
  \/ ServerPrewriteOptimistic
  \/ ServerPrewritePessimistic
  \/ ServerCommit
  \/ \E k \in KEY : ServerResolveLock(k)
  \/ Terminated

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants *)

TypeOK ==
  /\ next_ts \in Nat \ {0}
  /\ client_state \in [CLIENT -> ClientStates]
  /\ client_ts \in [CLIENT -> [start_ts : Nat, commit_ts : Nat, for_update_ts : Nat]]
  /\ client_key \in [CLIENT -> [locked : SUBSET KEY, prewrited : SUBSET KEY]]
  /\ client_read \in [CLIENT -> [KEY -> ReadRec]]
  /\ key_lock \in [KEY -> SUBSET LockRec]
  /\ \A k \in KEY : key_write[k] \in Seq(WriteRec)
  /\ req_msgs \subseteq MsgRec(ReqTypes)
  /\ resp_msgs \subseteq MsgRec(RespTypes)

UniqueCommitOrAbort ==
  \A k \in KEY : \A i, j \in DOMAIN key_write[k] :
    key_write[k][i].start_ts = key_write[k][j].start_ts => i = j

CommitConsistency ==
  \A c \in CLIENT : client_state[c] = "committed" =>
    /\ \E w \in Range(key_write[CLIENT_PRIMARY[c]]) :
         w.start_ts = StartTs(c) /\ w.type = "write" /\ w.ts = client_ts[c].commit_ts
    /\ \A k \in CLIENT_WRITE_KEY[c] :
         \/ OwnLock(k, StartTs(c)) # {}
         \/ \E w \in Records(k, StartTs(c)) :
              w.type = "write" /\ w.ts = client_ts[c].commit_ts

AbortConsistency ==
  \A c \in CLIENT : client_state[c] = "aborted" =>
    ~\E w \in Records(CLIENT_PRIMARY[c], StartTs(c)) : w.type = "write"

WriteConsistency ==
  \A k \in KEY : \A w \in Range(key_write[k]) : w.type = "write" =>
    \E c \in CLIENT :
      /\ StartTs(c) = w.start_ts
      /\ client_ts[c].commit_ts = w.ts
      /\ k \in CLIENT_WRITE_KEY[c]
      /\ client_state[c] \in {"committing", "committed"}

UniqueWrite ==
  \A k \in KEY : \A i, j \in DOMAIN key_write[k] :
    (i # j /\ key_write[k][i].type = "write" /\ key_write[k][j].type = "write")
      => key_write[k][i].ts # key_write[k][j].ts

UniqueLockOrWrite ==
  \A k \in KEY :
    /\ Cardinality(key_lock[k]) <= 1
    /\ \A l \in key_lock[k] : Records(k, l.ts) = {}

OptimisticReadSnapshotIsolation ==
  \A c \in OPTIMISTIC_CLIENT : \A k \in CLIENT_READ_KEY[c] :
    client_read[c][k].done =>
      client_read[c][k].val = SnapshotValue(k, StartTs(c))

PessimisticReadSnapshotIsolation ==
  \A c \in PESSIMISTIC_CLIENT : \A k \in CLIENT_READ_KEY[c] :
    client_read[c][k].done =>
      client_read[c][k].val = SnapshotValue(k, client_read[c][k].ts)

MsgTsConsistency ==
  \A m \in req_msgs :
    /\ m.start_ts > 0 /\ m.start_ts < next_ts
    /\ m.type = "lock_key" =>
         m.start_ts <= m.for_update_ts /\ m.for_update_ts < next_ts
    /\ m.type = "commit" =>
         m.start_ts < m.commit_ts /\ m.commit_ts < next_ts

=============================================================================
```