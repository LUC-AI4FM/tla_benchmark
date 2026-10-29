```tla
key[c].locking \cup client_key[c].prewriting :
       \E l \in key_lock[k] :
         /\ l.ts # client_ts[c].start_ts
         /\ SendReqs({Msg("check_txn_status", l.ts, l.primary, l.primary, 0, 0)})
  /\ UNCHANGED <<next_ts, client_vars, key_vars>>

-------------------------------------------------------------------------------
\* Server actions (requests are never removed; handlers are guarded to be idempotent)

ServerLockKey ==
  \E req \in msg_reqs :
    /\ req.type = "lock_key"
    /\ LET k == req.key
           sts == req.start_ts
       IN /\ key_lock[k] = {}
          /\ ~\E w \in key_write[k] : w.start_ts = sts
          /\ ~\E w \in key_write[k] : w.type = "write" /\ w.ts > req.for_update_ts
          /\ key_lock' = [key_lock EXCEPT ![k] =
                {[ts |-> sts, primary |-> req.primary, type |-> "lock_key",
                  for_update_ts |-> req.for_update_ts]}]
    /\ UNCHANGED <<next_ts, msg_reqs, client_vars, key_write, key_data>>

ServerPrewritePessimistic ==
  \E req \in msg_reqs :
    /\ req.type = "prewrite_pessimistic"
    /\ LET k == req.key
           sts == req.start_ts
       IN \E l \in key_lock[k] :
            /\ l.ts = sts
            /\ l.type = "lock_key"
            /\ key_lock' = [key_lock EXCEPT ![k] =
                  {[ts |-> sts, primary |-> req.primary, type |-> "prewrite_pessimistic",
                    for_update_ts |-> l.for_update_ts]}]
            /\ key_data' = [key_data EXCEPT ![k] = @ \cup {[ts |-> sts]}]
    /\ UNCHANGED <<next_ts, msg_reqs, client_vars, key_write>>

ServerPrewriteOptimistic ==
  \E req \in msg_reqs :
    /\ req.type = "prewrite_optimistic"
    /\ LET k == req.key
           sts == req.start_ts
       IN /\ key_lock[k] = {}
          /\ ~\E w \in key_write[k] : w.start_ts = sts
          /\ ~\E w \in key_write[k] : w.type = "write" /\ w.ts > sts
          /\ key_lock' = [key_lock EXCEPT ![k] =
                {[ts |-> sts, primary |-> req.primary, type |-> "prewrite_optimistic",
                  for_update_ts |-> 0]}]
          /\ key_data' = [key_data EXCEPT ![k] = @ \cup {[ts |-> sts]}]
    /\ UNCHANGED <<next_ts, msg_reqs, client_vars, key_write>>

\* Commit the primary key; secondaries are committed asynchronously via resolve_committed.
ServerCommit ==
  \E req \in msg_reqs :
    /\ req.type = "commit"
    /\ LET k == req.primary
           sts == req.start_ts
       IN \E l \in key_lock[k] :
            /\ l.ts = sts
            /\ l.type # "lock_key"
            /\ key_lock' = [key_lock EXCEPT ![k] = @ \ {l}]
            /\ key_write' = [key_write EXCEPT ![k] =
                  @ \cup {[ts |-> req.commit_ts, start_ts |-> sts, type |-> "write"]}]
            /\ SendReqs({Msg("resolve_committed", sts, k, k, 0, req.commit_ts)})
    /\ UNCHANGED <<next_ts, client_vars, key_data>>

ServerResolveCommitted ==
  \E req \in msg_reqs :
    /\ req.type = "resolve_committed"
    /\ \E k \in KEY : \E l \in key_lock[k] :
         /\ l.ts = req.start_ts
         /\ key_lock' = [key_lock EXCEPT ![k] = @ \ {l}]
         /\ IF l.type = "lock_key"
              THEN UNCHANGED key_write
              ELSE key_write' = [key_write EXCEPT ![k] =
                     @ \cup {[ts |-> req.commit_ts, start_ts |-> req.start_ts, type |-> "write"]}]
    /\ UNCHANGED <<next_ts, msg_reqs, client_vars, key_data>>

ServerResolveRollbacked ==
  \E req \in msg_reqs :
    /\ req.type = "resolve_rollbacked"
    /\ \E k \in KEY : \E l \in key_lock[k] :
         /\ l.ts = req.start_ts
         /\ key_lock' = [key_lock EXCEPT ![k] = @ \ {l}]
         /\ key_write' = [key_write EXCEPT ![k] =
               @ \cup {[ts |-> req.start_ts, start_ts |-> req.start_ts, type |-> "rollback"]}]
    /\ UNCHANGED <<next_ts, msg_reqs, client_vars, key_data>>
```

```tla
\* TTL is abstracted as always expired when checked.
ServerCheckTxnStatus ==
  \E req \in msg_reqs :
    /\ req.type = "check_txn_status"
    /\ LET k == req.primary
           sts == req.start_ts
           committed == {w \in key_write[k] : w.start_ts = sts /\ w.type = "write"}
       IN \/ /\ committed # {}
             /\ \E w \in committed :
                  SendReqs({Msg("resolve_committed", sts, k, k, 0, w.ts)})
             /\ UNCHANGED key_vars
          \/ /\ \E w \in key_write[k] : w.start_ts = sts /\ w.type = "rollback"
             /\ SendReqs({Msg("resolve_rollbacked", sts, k, k, 0, 0)})
             /\ UNCHANGED key_vars
          \/ /\ ~\E w \in key_write[k] : w.start_ts = sts
             /\ key_lock' = [key_lock EXCEPT ![k] = {l \in @ : l.ts # sts}]
             /\ key_write' = [key_write EXCEPT ![k] =
                   @ \cup {[ts |-> sts, start_ts |-> sts, type |-> "rollback"]}]
             /\ SendReqs({Msg("resolve_rollbacked", sts, k, k, 0, 0)})
             /\ UNCHANGED key_data
    /\ UNCHANGED <<next_ts, client_vars>>

-------------------------------------------------------------------------------
Next ==
  \/ \E c \in CLIENT :
       \/ ClientLockKey(c)
       \/ ClientLockedKey(c)
       \/ ClientRetryLockKey(c)
       \/ ClientPrewritePessimistic(c)
       \/ ClientPrewriteOptimistic(c)
       \/ ClientPrewrited(c)
       \/ ClientCommit(c)
       \/ ClientCommitted(c)
       \/ ClientAbort(c)
       \/ ClientCheckTxnStatus(c)
  \/ ServerLockKey
  \/ ServerPrewritePessimistic
  \/ ServerPrewriteOptimistic
  \/ ServerCommit
  \/ ServerResolveCommitted
  \/ ServerResolveRollbacked
  \/ ServerCheckTxnStatus

Spec == Init /\ [][Next]_vars

-------------------------------------------------------------------------------
\* Safety invariants

TypeOK ==
  /\ next_ts \in Nat \ {0}
  /\ client_state \in [CLIENT -> ClientStates]
  /\ client_ts \in [CLIENT -> [start_ts : Nat, commit_ts : Nat, for_update_ts : Nat]]
  /\ client_key \in [CLIENT -> [locking : SUBSET KEY, prewriting : SUBSET KEY]]
  /\ \A k \in KEY :
       /\ key_lock[k] \subseteq [ts : Nat, primary : KEY, type : LockTypes, for_update_ts : Nat]
       /\ Cardinality(key_lock[k]) <= 1
       /\ key_write[k] \subseteq [ts : Nat, start_ts : Nat, type : WriteTypes]
       /\ key_data[k] \subseteq [ts : Nat]
  /\ msg_reqs \subseteq [type : MsgTypes, start_ts : Nat, primary : KEY, key : KEY,
                         for_update_ts : Nat, commit_ts : Nat]

\* A committed transaction is never rolled back, and an aborted one never committed.
CommitConsistency ==
  \A c \in CLIENT :
    LET sts == client_ts[c].start_ts IN
    /\ client_state[c] = "committed" =>
         /\ \E w \in key_write[CLIENT_PRIMARY[c]] :
              w.start_ts = sts /\ w.type = "write" /\ w.ts = client_ts[c].commit_ts
         /\ \A k \in KEY : ~\E w \in key_write[k] : w.start_ts = sts /\ w.type = "rollback"
    /\ client_state[c] = "aborted" =>
         \A k \in KEY : ~\E w \in key_write[k] : w.start_ts = sts /\ w.type = "write"

\* A lock never coexists with a write record of the same transaction; data backs locks/writes.
LockWriteConsistency ==
  \A k \in KEY :
    /\ \A l \in key_lock[k] :
         /\ ~\E w \in key_write[k] : w.start_ts = l.ts
         /\ l.type # "lock_key" => [ts |-> l.ts] \in key_data[k]
    /\ \A w \in key_write[k] : w.type = "write" => [ts |-> w.start_ts] \in key_data[k]

\* Each transaction has at most one write record per key, and timestamps are unique.
UniquenessConsistency ==
  \A k \in KEY : \A w1, w2 \in key_write[k] :
    /\ w1.start_ts = w2.start_ts => w1 = w2
    /\ w1.ts = w2.ts => w1 = w2

UniqueClientTs ==
  \A c1, c2 \in CLIENT :
    (c1 # c2 /\ client_state[c1] # "init" /\ client_state[c2] # "init")
      => client_ts[c1].start_ts # client_ts[c2].start_ts

MsgTsConsistency ==
  \A req \in msg_reqs :
    /\ 0 < req.start_ts /\ req.start_ts < next_ts
    /\ req.type \in {"commit", "resolve_committed"} =>
         req.start_ts < req.commit_ts /\ req.commit_ts < next_ts
    /\ req.type = "lock_key" =>
         req.start_ts <= req.for_update_ts /\ req.for_update_ts < next_ts

\* No other transaction commits a write on our keys between start_ts and commit_ts.
OptimisticSnapshotIsolation ==
  \A c \in OPTIMISTIC_CLIENT :
    client_state[c] = "committed" =>
      \A k \in CLIENT_KEY[c] : \A w \in key_write[k] :
        (w.type = "write" /\ w.start_ts # client_ts[c].start_ts) =>
          (w.ts < client_ts[c].start_ts \/ w.ts > client_ts[c].commit_ts)

\* No other transaction commits a write on our keys between for_update_ts and commit_ts.
PessimisticSnapshotIsolation ==
  \A c \in PESSIMISTIC_CLIENT :
    client_state[c] = "committed" =>
      \A k \in CLIENT_KEY[c] : \A w \in key_write[k] :
        (w.type = "write" /\ w.start_ts # client_ts[c].start_ts) =>
          (w.ts < client_ts[c].for_update_ts \/ w.ts > client_ts[c].commit_ts)

Safety ==
  /\ TypeOK
  /\ CommitConsistency
  /\ LockWriteConsistency
  /\ UniquenessConsistency
  /\ UniqueClientTs
  /\ MsgTsConsistency
  /\ OptimisticSnapshotIsolation
  /\ PessimisticSnapshotIsolation

THEOREM Spec => []Safety
===============================================================================
```