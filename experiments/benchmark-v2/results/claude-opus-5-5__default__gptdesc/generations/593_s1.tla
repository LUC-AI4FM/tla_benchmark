------------------------------------------------------------
(* Client actions. Responses are modeled as atomic client steps that
   directly observe the server state. *)

ClientStartOptimistic(c) ==
  /\ client_state[c] = "init"
  /\ client_state' = [client_state EXCEPT ![c] = "prewriting"]
  /\ client_ts' = [client_ts EXCEPT ![c] =
                     [start_ts |-> next_ts, commit_ts |-> 0, for_update_ts |-> next_ts]]
  /\ next_ts' = next_ts + 1
  /\ SendReqs({[cmd |-> "prewrite_optimistic", start_ts |-> next_ts,
                primary |-> CLIENT_PRIMARY[c], key |-> k] : k \in CLIENT_KEY[c]})
  /\ UNCHANGED key_vars

ClientStartPessimistic(c) ==
  /\ client_state[c] = "init"
  /\ client_state' = [client_state EXCEPT ![c] = "locking"]
  /\ client_ts' = [client_ts EXCEPT ![c] =
                     [start_ts |-> next_ts, commit_ts |-> 0, for_update_ts |-> next_ts]]
  /\ next_ts' = next_ts + 1
  /\ SendReqs({[cmd |-> "lock_key", start_ts |-> next_ts, primary |-> CLIENT_PRIMARY[c],
                key |-> k, for_update_ts |-> next_ts] : k \in CLIENT_KEY[c]})
  /\ UNCHANGED key_vars

\* A pessimistic lock failed due to a newer committed write: retry with a
\* fresh for_update_ts.
ClientRetryLockKey(c) ==
  LET s == client_ts[c].start_ts
      f == client_ts[c].for_update_ts
  IN /\ client_state[c] = "locking"
     /\ \E k \in CLIENT_KEY[c] :
          /\ ~\E l \in key_lock[k] : l.ts = s
          /\ \E w \in key_write[k] : w.type = "write" /\ w.ts >= f
     /\ client_ts' = [client_ts EXCEPT ![c].for_update_ts = next_ts]
     /\ next_ts' = next_ts + 1
     /\ SendReqs({[cmd |-> "lock_key", start_ts |-> s, primary |-> CLIENT_PRIMARY[c],
                   key |-> k, for_update_ts |-> next_ts] : k \in CLIENT_KEY[c]})
     /\ UNCHANGED <<client_state, key_vars>>

ClientLockedKey(c) ==
  LET s == client_ts[c].start_ts
  IN /\ client_state[c] = "locking"
     /\ \A k \in CLIENT_KEY[c] : HasLockOfType(k, s, "lock_key")
     /\ client_state' = [client_state EXCEPT ![c] = "prewriting"]
     /\ SendReqs({[cmd |-> "prewrite_pessimistic", start_ts |-> s,
                   primary |-> CLIENT_PRIMARY[c], key |-> k] : k \in CLIENT_KEY[c]})
     /\ UNCHANGED <<next_ts, client_ts, key_vars>>

ClientPrewrited(c) ==
  LET s  == client_ts[c].start_ts
      tp == IF c \in OPTIMISTIC_CLIENT THEN "prewrite_optimistic" ELSE "prewrite_pessimistic"
  IN /\ client_state[c] = "prewriting"
     /\ \A k \in CLIENT_KEY[c] : HasLockOfType(k, s, tp)
     /\ client_state' = [client_state EXCEPT ![c] = "committing"]
     /\ client_ts' = [client_ts EXCEPT ![c].commit_ts = next_ts]
     /\ next_ts' = next_ts + 1
     /\ SendReqs({[cmd |-> "commit", start_ts |-> s, primary |-> CLIENT_PRIMARY[c],
                   commit_ts |-> next_ts]})
     /\ UNCHANGED key_vars

ClientCommitted(c) ==
  LET s == client_ts[c].start_ts
  IN /\ client_state[c] = "committing"
     /\ HasWriteOfType(CLIENT_PRIMARY[c], s, "write")
     /\ client_state' = [client_state EXCEPT ![c] = "committed"]
     /\ SendReqs({[cmd |-> "resolve_committed", start_ts |-> s,
                   commit_ts |-> client_ts[c].commit_ts]})
     /\ UNCHANGED <<next_ts, client_ts, key_vars>>

\* Client gives up (e.g. on conflict) before sending commit and asks the
\* primary to roll the transaction back.
ClientAbort(c) ==
  /\ client_state[c] \in {"locking", "prewriting"}
  /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
  /\ SendReqs({[cmd |-> "check_txn_status", start_ts |-> client_ts[c].start_ts,
                primary |-> CLIENT_PRIMARY[c]]})
  /\ UNCHANGED <<next_ts, client_ts, key_vars>>

\* Client observes that its transaction was rolled back by lock resolution.
ClientRolledBack(c) ==
  /\ client_state[c] \in {"locking", "prewriting", "committing"}
  /\ HasWriteOfType(CLIENT_PRIMARY[c], client_ts[c].start_ts, "rollback")
  /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
  /\ UNCHANGED <<next_ts, client_ts, key_vars, req_msgs>>

-----------------------------------------------------------------------------
(* Server actions. Any sent request may be (re)processed at any time. *)

ServerLockKey ==
  \E m \in req_msgs :
    /\ m.cmd = "lock_key"
    /\ LET k == m.key
           s == m.start_ts
           f == m.for_update_ts
       IN /\ ~\E w \in key_write[k] : w.start_ts = s
          /\ ~\E w \in key_write[k] : w.type = "write" /\ w.ts >= f
          /\ IF key_lock[k] = {}
             THEN /\ key_lock' = [key_lock EXCEPT ![k] =
                        {[ts |-> s, primary |-> m.primary, type |-> "lock_key",
                          for_update_ts |-> f]}]
                  /\ UNCHANGED req_msgs
             ELSE /\ \E l \in key_lock[k] : l.ts # s
                  /\ SendReqs(CheckLockOwners(k))
                  /\ UNCHANGED key_lock
    /\ UNCHANGED <<next_ts, client_vars, key_write, key_data>>

ServerPrewriteOptimistic ==
  \E m \in req_msgs :
    /\ m.cmd = "prewrite_optimistic"
    /\ LET k == m.key
           s == m.start_ts
       IN /\ ~\E w \in key_write[k] : w.ts >= s
          /\ IF key_lock[k] = {}
             THEN /\ key_lock' = [key_lock EXCEPT ![k] =
                        {[ts |-> s, primary |-> m.primary, type |-> "prewrite_optimistic",
                          for_update_ts |-> s]}]
                  /\ key_data' = [key_data EXCEPT ![k] = @ \cup {s}]
                  /\ UNCHANGED req_msgs
             ELSE /\ \E l \in key_lock[k] : l.ts # s
                  /\ SendReqs(CheckLockOwners(k))
                  /\ UNCHANGED <<key_lock, key_data>>
    /\ UNCHANGED <<next_ts, client_vars, key_write>>

ServerPrewritePessimistic ==
  \E m \in req_msgs :
    /\ m.cmd = "prewrite_pessimistic"
    /\ LET k == m.key
           s == m.start_ts
       IN /\ HasLockOfType(k, s, "lock_key")
          /\ LET lk == CHOOSE l \in key_lock[k] : l.ts = s
             IN key_lock' = [key_lock EXCEPT ![k] =
                   {[ts |-> s, primary |-> m.primary, type |-> "prewrite_pessimistic",
                     for_update_ts |-> lk.for_update_ts]}]
          /\ key_data' = [key_data EXCEPT ![k] = @ \cup {s}]
    /\ UNCHANGED <<next_ts, client_vars, key_write, req_msgs>>

ServerCommit ==
  \E m \in req_msgs :
    /\ m.cmd = "commit"
    /\ LET p == m.primary
           s == m.start_ts
       IN /\ \E l \in key_lock[p] : l.ts = s /\ l.type # "lock_key"
          /\ key_lock' = [key_lock EXCEPT ![p] = {l \in @ : l.ts # s}]
          /\ key_write' = [key_write EXCEPT ![p] =
                @ \cup {[ts |-> m.commit_ts, start_ts |-> s, type |-> "write"]}]
    /\ UNCHANGED <<next_ts, client_vars, key_data, req_msgs>>

ServerCheckTxnStatus ==
  \E m \in req_msgs :
    /\ m.cmd = "check_txn_status"
    /\ LET p == m.primary
           s == m.start_ts
           commits == {w \in key_write[p] : w.start_ts = s /\ w.type = "write"}
           rollbacks == {w \in key_write[p] : w.start_ts = s /\ w.type = "rollback"}
       IN IF commits # {}
          THEN /\ SendReqs({[cmd |-> "resolve_committed", start_ts |-> s,
                             commit_ts |-> (CHOOSE w \in commits : TRUE).ts]})
               /\ UNCHANGED key_vars
          ELSE IF rollbacks # {}
          THEN /\ SendReqs({[cmd |-> "resolve_rollbacked", start_ts |-> s]})
               /\ UNCHANGED key_vars
          ELSE \* TTL abstracted as expired: roll back the primary.
               /\ key_lock' = [key_lock EXCEPT ![p] = {l \in @ : l.ts # s}]
               /\ key_write' = [key_write EXCEPT ![p] =
                     @ \cup {[ts |-> s, start_ts |-> s, type |-> "rollback"]}]
               /\ SendReqs({[cmd |-> "resolve_rollbacked", start_ts |-> s]})
               /\ UNCHANGED key_data
    /\ UNCHANGED <<next_ts, client_vars>>

ServerResolveCommitted ==
  \E m \in req_msgs, k \in KEY :
    /\ m.cmd = "resolve_committed"
    /\ \E l \in key_lock[k] : l.ts = m.start_ts
    /\ LET lk == CHOOSE l \in key_lock[k] : l.ts = m.start_ts
       IN /\ key_lock' = [key_lock EXCEPT ![k] = @ \ {lk}]
          /\ key_write' = IF lk.type = "lock_key"
                          THEN key_write
                          ELSE [key_write EXCEPT ![k] =
                                 @ \cup {[ts |-> m.commit_ts, start_ts |-> m.start_ts,
                                          type |-> "write"]}]
    /\ UNCHANGED <<next_ts, client_vars, key_data, req_msgs>>

ServerResolveRollbacked ==
  \E m \in req_msgs, k \in KEY :
    /\ m.cmd = "resolve_rollbacked"
    /\ \E l \in key_lock[k] : l.ts = m.start_ts
    /\ key_lock' = [key_lock EXCEPT ![k] = {l \in @ : l.ts # m.start_ts}]
    /\ key_write' = [key_write EXCEPT ![k] =
          @ \cup {[ts |-> m.start_ts, start_ts |-> m.start_ts, type |-> "rollback"]}]
    /\ UNCHANGED <<next_ts, client_vars, key_data, req_msgs>>

-----------------------------------------------------------------------------
Next ==
  \/ \E c \in OPTIMISTIC_CLIENT :
       \/ ClientStartOptimistic(c)
       \/ ClientPrewrited(c)
       \/ ClientCommitted(c)
       \/ ClientAbort(c)
       \/ ClientRolledBack(c)
  \/ \E c \in PESSIMISTIC_CLIENT :
       \/ ClientStartPessimistic(c)
       \/ ClientRetryLockKey(c)
       \/ ClientLockedKey(c)
       \/ ClientPrewrited(c)
       \/ ClientCommitted(c)
       \/ ClientAbort(c)
       \/ ClientRolledBack(c)
  \/ ServerLockKey
  \/ ServerPrewriteOptimistic
  \/ ServerPrewritePessimistic
  \/ ServerCommit
  \/ ServerCheckTxnStatus
  \/ ServerResolveCommitted
  \/ ServerResolveRollbacked

\* Safety-focused specification: no fairness assumptions.
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety invariants *)

TypeOK ==
  /\ next_ts \in Nat \ {0}
  /\ client_state \in [CLIENT -> ClientStates]
  /\ client_ts \in [CLIENT -> [start_ts : Nat, commit_ts : Nat, for_update_ts : Nat]]
  /\ key_lock \in [KEY -> SUBSET LockRec]
  /\ key_write \in [KEY -> SUBSET WriteRec]
  /\ key_data \in [KEY -> SUBSET Nat]
  /\ req_msgs \subseteq ReqMessages

\* Commit / abort consistency.
CommittedConsistency ==
  \A c \in CLIENT :
    client_state[c] = "committed" =>
      /\ HasWriteOfType(CLIENT_PRIMARY[c], client_ts[c].start_ts, "write")
      /\ ~\E k \in KEY : HasWriteOfType(k, client_ts[c].start_ts, "rollback")

AbortedConsistency ==
  \A c \in CLIENT :
    client_state[c] = "aborted" =>
      ~\E k \in KEY : HasWriteOfType(k, client_ts[c].start_ts, "write")

\* A transaction is never both committed on one key and rolled back on another.
CommitRollbackConsistency ==
  \A k1, k2 \in KEY :
    \A w1 \in key_write[k1], w2 \in key_write[k2] :
      w1.start_ts = w2.start_ts => w1.type = w2.type

\* Lock / write consistency.
LockWriteConsistency ==
  \A k \in KEY :
    /\ \A l \in key_lock[k] : ~\E w \in key_write[k] : w.start_ts = l.ts
    /\ \A l \in key_lock[k] : l.type # "lock_key" => l.ts \in key_data[k]
    /\ \A w \in key_write[k] : w.type = "write" => w.start_ts \in key_data[k]

\* Uniqueness properties.
UniqueLockPerKey == \A k \in KEY : Cardinality(key_lock[k]) <= 1

UniqueWrite ==
  \A k \in KEY : \A w1, w2 \in key_write[k] :
    /\ w1.ts = w2.ts => w1 = w2
    /\ w1.start_ts = w2.start_ts => w1 = w2

UniqueTimestamps ==
  \A c1, c2 \in CLIENT :
    c1 # c2 =>
      /\ client_ts[c1].start_ts > 0 => client_ts[c1].start_ts # client_ts[c2].start_ts
      /\ client_ts[c1].commit_ts > 0 => client_ts[c1].commit_ts # client_ts[c2].commit_ts
      /\ client_ts[c1].commit_ts > 0 => client_ts[c1].commit_ts # client_ts[c2].start_ts

\* Message timestamp consistency.
MsgTsConsistency ==
  \A m \in req_msgs :
    /\ m.start_ts > 0
    /\ m.start_ts < next_ts
    /\ \E c \in CLIENT : client_ts[c].start_ts = m.start_ts
    /\ m.cmd = "lock_key" => m.for_update_ts >= m.start_ts
    /\ m.cmd \in {"commit", "resolve_committed"} =>
         /\ m.commit_ts > m.start_ts
         /\ \E c \in CLIENT : /\ client_ts[c].start_ts = m.start_ts
                              /\ client_ts[c].commit_ts = m.commit_ts

\* Snapshot isolation: no other committed write to a key lands between the
\* transaction's read point (start_ts / for_update_ts) and its commit_ts.
OptimisticSnapshotIsolation ==
  \A c \in OPTIMISTIC_CLIENT :
    client_state[c] = "committed" =>
      \A k \in CLIENT_KEY[c] : \A w \in key_write[k] :
        (w.type = "write" /\ w.start_ts # client_ts[c].start_ts) =>
          (w.ts < client_ts[c].start_ts \/ w.ts > client_ts[c].commit_ts)

PessimisticSnapshotIsolation ==
  \A c \in PESSIMISTIC_CLIENT :
    client_state[c] = "committed" =>
      \A k \in CLIENT_KEY[c] : \A w \in key_write[k] :
        (w.type = "write" /\ w.start_ts # client_ts[c].start_ts) =>
          (w.ts < client_ts[c].for_update_ts \/ w.ts > client_ts[c].commit_ts)

Safety ==
  /\ TypeOK
  /\ CommittedConsistency
  /\ AbortedConsistency
  /\ CommitRollbackConsistency
  /\ LockWriteConsistency
  /\ UniqueLockPerKey
  /\ UniqueWrite
  /\ UniqueTimestamps
  /\ MsgTsConsistency
  /\ OptimisticSnapshotIsolation
  /\ PessimisticSnapshotIsolation

THEOREM Spec => []Safety
=============================================================================