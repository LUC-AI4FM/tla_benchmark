```tla
k, ts) == \E l \in key_lock[k] : l.ts = ts

PrewriteOrder(c, k) ==
  k = CLIENT_PRIMARY[c] \/ CLIENT_PRIMARY[c] \notin client_pending[c]

Abort(c) ==
  /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
  /\ client_pending' = [client_pending EXCEPT ![c] = {}]

-----------------------------------------------------------------------------
Init ==
  /\ next_ts = 1
  /\ client_state = [c \in CLIENT |-> "init"]
  /\ client_ts = [c \in CLIENT |-> [start_ts |-> 0, for_update_ts |-> 0,
                                    min_commit_ts |-> 0, commit_ts |-> 0]]
  /\ client_read = [c \in CLIENT |-> {}]
  /\ client_pending = [c \in CLIENT |-> {}]
  /\ key_lock = [k \in KEY |-> {}]
  /\ key_write = [k \in KEY |-> {}]
  /\ key_data = [k \in KEY |-> {}]
  /\ key_last_read_ts = [k \in KEY |-> 0]

-----------------------------------------------------------------------------
(* Client: obtain start_ts (and for_update_ts for pessimistic clients). *)
Start(c) ==
  /\ client_state[c] = "init"
  /\ client_pending' = [client_pending EXCEPT ![c] = CLIENT_KEY[c]]
  /\ IF c \in OPTIMISTIC_CLIENT
     THEN /\ client_ts' = [client_ts EXCEPT ![c].start_ts = next_ts]
          /\ next_ts' = next_ts + 1
          /\ client_state' = [client_state EXCEPT ![c] = "reading"]
     ELSE /\ client_ts' = [client_ts EXCEPT ![c].start_ts = next_ts,
                                            ![c].for_update_ts = next_ts + 1]
          /\ next_ts' = next_ts + 2
          /\ client_state' = [client_state EXCEPT ![c] = "locking"]
  /\ UNCHANGED <<client_read, key_lock, key_write, key_data, key_last_read_ts>>

(* Optimistic: snapshot read at start_ts. Blocks on prewrite locks older *)
(* than the snapshot; those must be resolved first.                      *)
OptRead(c, k) ==
  LET ts == client_ts[c].start_ts IN
  /\ c \in OPTIMISTIC_CLIENT
  /\ client_state[c] = "reading"
  /\ k \in client_pending[c]
  /\ ~ \E l \in key_lock[k] : l.type = "prewrite" /\ l.ts <= ts
  /\ client_read' = [client_read EXCEPT ![c] =
                        @ \cup {[key |-> k, val |-> LatestWrite(k, ts)]}]
  /\ key_last_read_ts' = [key_last_read_ts EXCEPT ![k] = Max({@, ts})]
  /\ IF client_pending[c] = {k}
     THEN /\ client_state' = [client_state EXCEPT ![c] = "prewriting"]
          /\ client_pending' = [client_pending EXCEPT ![c] = CLIENT_KEY[c]]
     ELSE /\ client_pending' = [client_pending EXCEPT ![c] = @ \ {k}]
          /\ UNCHANGED client_state
  /\ UNCHANGED <<next_ts, client_ts, key_lock, key_write, key_data>>

(* Optimistic: prewrite (primary first), with write-conflict detection. *)
OptPrewrite(c, k) ==
  LET ts  == client_ts[c].start_ts
      mct == Max({ts + 1, key_last_read_ts[k] + 1})
  IN
  /\ c \in OPTIMISTIC_CLIENT
  /\ client_state[c] = "prewriting"
  /\ k \in client_pending[c]
  /\ PrewriteOrder(c, k)
  /\ \/ /\ OptConflict(k, ts)
        /\ Abort(c)
        /\ UNCHANGED <<next_ts, client_ts, client_read, key_lock, key_write,
                       key_data, key_last_read_ts>>
     \/ /\ ~ OptConflict(k, ts)
        /\ key_lock[k] = {}
        /\ key_lock' = [key_lock EXCEPT ![k] =
              {[ts |-> ts, primary |-> CLIENT_PRIMARY[c], type |-> "prewrite",
                for_update_ts |-> 0, min_commit_ts |-> mct]}]
        /\ key_data' = [key_data EXCEPT ![k] = @ \cup {ts}]
        /\ client_ts' = [client_ts EXCEPT ![c].min_commit_ts = Max({@, mct})]
        /\ client_pending' = [client_pending EXCEPT ![c] = @ \ {k}]
        /\ UNCHANGED <<next_ts, client_state, client_read, key_write,
                       key_last_read_ts>>

(* Pessimistic: acquire a pessimistic lock (primary first), reading the  *)
(* value at for_update_ts during acquisition.                            *)
PessLock(c, k) ==
  LET ts  == client_ts[c].start_ts
      fut == client_ts[c].for_update_ts
  IN
  /\ c \in PESSIMISTIC_CLIENT
  /\ client_state[c] = "locking"
  /\ k \in client_pending[c]
  /\ PrewriteOrder(c, k)
  /\ \/ /\ PessConflict(k, ts, fut)
        /\ Abort(c)
        /\ UNCHANGED <<next_ts, client_ts, client_read, key_lock, key_write,
                       key_data, key_last_read_ts>>
     \/ /\ ~ PessConflict(k, ts, fut)
        /\ key_lock[k] = {}
        /\ key_lock' = [key_lock EXCEPT ![k] =
              {[ts |-> ts, primary |-> CLIENT_PRIMARY[c], type |-> "pessimistic",
                for_update_ts |-> fut, min_commit_ts |-> 0]}]
        /\ client_read' = [client_read EXCEPT ![c] =
                              @ \cup {[key |-> k, val |-> LatestWrite(k, fut)]}]
        /\ key_last_read_ts' = [key_last_read_ts EXCEPT ![k] = Max({@, fut})]
        /\ IF client_pending[c] = {k}
           THEN /\ client_state' = [client_state EXCEPT ![c] = "prewriting"]
                /\ client_pending' = [client_pending EXCEPT ![c] = CLIENT_KEY[c]]
           ELSE /\ client_pending' = [client_pending EXCEPT ![c] = @ \ {k}]
                /\ UNCHANGED client_state
        /\ UNCHANGED <<next_ts, client_ts, key_write, key_data>>

(* Pessimistic: convert a pessimistic lock into a prewrite lock. If the  *)
(* lock was lost (rolled back by a resolver), the transaction aborts.    *)
PessPrewrite(c, k) ==
  LET ts  == client_ts[c].start_ts
      fut == client_ts[c].for_update_ts
      mct == Max({ts + 1, fut + 1, key_last_read_ts[k] + 1})
  IN
  /\ c \in PESSIMISTIC_CLIENT
  /\ client_state[c] = "prewriting"
  /\ k \in client_pending[c]
  /\ PrewriteOrder(c, k)
  /\ \/ /\ \E l \in key_lock[k] : l.ts = ts /\ l.type = "pessimistic"
        /\ key_lock' = [key_lock EXCEPT ![k] =
              {[ts |-> ts, primary |-> CLIENT_PRIMARY[c], type |-> "prewrite",
                for_update_ts |-> fut, min_commit_ts |-> mct]}]
        /\ key_data' = [key_data EXCEPT ![k] = @ \cup {ts}]
        /\ client_ts' = [client_ts EXCEPT ![c].min_commit_ts = Max({@, mct})]
        /\ client_pending' = [client_pending EXCEPT ![c] = @ \ {k}]
        /\ UNCHANGED <<next_ts, client_state, client_read, key_write,
                       key_last_read_ts>>
     \/ /\ ~ HasLock(k, ts)
        /\ Abort(c)
        /\ UNCHANGED <<next_ts, client_ts, client_read, key_lock, key_write,
                       key_data, key_last_read_ts>>

(* Obtain a commit timestamp that respects min_commit_ts. *)
GetCommitTs(c) ==
  LET cts == Max({next_ts, client_ts[c].min_commit_ts}) IN
  /\ client_state[c] = "prewriting"
  /\ client_pending[c] = {}
  /\ client_ts' = [client_ts EXCEPT ![c].commit_ts = cts]
  /\ next_ts' = cts + 1
  /\ client_state' = [client_state EXCEPT ![c] = "committing"]
  /\ UNCHANGED <<client_read, client_pending, key_lock, key_write, key_data,
                 key_last_read_ts>>

(* Commit the primary key: this is the atomic commit point. *)
CommitPrimary(c) ==
  LET p  == CLIENT_PRIMARY[c]
      ts == client_ts[c].start_ts
  IN
  /\ client_state[c] = "committing"
  /\ IF \E l \in key_lock[p] : l.ts = ts /\ l.type = "prewrite"
     THEN /\ key_lock' = [key_lock EXCEPT ![p] = {}]
          /\ key_write' = [key_write EXCEPT ![p] = @ \cup
                {[start_ts |-> ts, commit_ts |-> client_ts[c].commit_ts,
                  type |-> "write"]}]
          /\ client_state' = [client_state EXCEPT ![c] = "committed"]
          /\ client_pending' = [client_pending EXCEPT ![c] = SecondaryKeys(c)]
     ELSE /\ Abort(c)
          /\ UNCHANGED <<key_lock, key_write>>
  /\ UNCHANGED <<next_ts, client_ts, client_read, key_data, key_last_read_ts>>

(* Commit secondary keys after the primary is committed. *)
CommitSecondary(c, k) ==
  LET ts == client_ts[c].start_ts IN
  /\ client_state[c] = "committed"
  /\ k \in client_pending[c]
  /\ IF HasLock(k, ts)
     THEN /\ key_lock' = [key_lock EXCEPT ![k] = {}]
          /\ key_write' = [key_write EXCEPT ![k] = @ \cup
                {[start_ts |-> ts, commit_ts |-> client_ts[c].commit_ts,
                  type |-> "write"]}]
     ELSE UNCHANGED <<key_lock, key_write>>
  /\ client_pending' = [client_pending EXCEPT ![c] = @ \ {k}]
  /\ UNCHANGED <<next_ts, client_state, client_ts, client_read, key_data,
                 key_last_read_ts>>

(* Crash or lost message: the client stops mid-transaction, leaving locks. *)
Crash(c) ==
  \/ /\ client_state[c] \in {"init", "reading", "locking", "prewriting",
                             "committing"}
     /\ client_state' = [client_state EXCEPT ![c] = "crashed"]
     /\ client_pending' = [client_pending EXCEPT ![c] = {}]
     /\ UNCHANGED <<next_ts, client_ts, client_read, key_lock, key_write,
                    key_data, key_last_read_ts>>
  \/ /\ client_state[c] = "committed"
     /\ client_pending[c] # {}
     /\ client_pending' = [client_pending EXCEPT ![c] = {}]
     /\ UNCHANGED <<next_ts, client_state, client_ts, client_read, key_lock,
                    key_write, key_data, key_last_read_ts>>

-----------------------------------------------------------------------------
(* Lock resolution, performed by any transaction that meets a lock.     *)

\* Primary is committed: roll the secondary lock forward.
ResolveCommitted(k) ==
  \E l \in key_lock[k] :
    \E w \in key_write[l.primary] :
      /\ l.type = "prewrite"
      /\ w.start_ts = l.ts
      /\ w.type = "write"
      /\ key_lock' = [key_lock EXCEPT ![k] = {}]
      /\ key_write' = [key_write EXCEPT ![k] = @ \cup
            {[start_ts |-> l.ts, commit_ts |-> w.commit_ts, type |-> "write"]}]
      /\ UNCHANGED <<next_ts, client_state, client_ts, client_read,
                     client_pending, key_data, key_last_read_ts>>

\* Primary is rolled back: remove the lock and leave a rollback marker.
ResolveRolledBack(k) ==
  \E l \in key_lock[k] :
    /\ RolledBack(l.primary, l.ts)
    /\ key_lock' = [key_lock EXCEPT ![k] = {}]
    /\ key_write' = [key_write EXCEPT ![k] = @ \cup
          {[start_ts |-> l.ts, commit_ts |-> l.ts, type |-> "rollback"]}]
    /\ key_data' = [key_data EXCEPT ![k] = @ \ {l.ts}]
    /\ UNCHANGED <<next_ts, client_state, client_ts, client_read,
                   client_pending, key_last_read_ts>>

\* Primary undecided and the holder is presumed failed (TTL expired):
\* roll back the primary and write a rollback marker against zombie writes.
RollbackPrimary(k) ==
  \E l \in key_lock[k] :
    LET p  == l.primary
        ts == l.ts
    IN
    /\ ~ \E w \in key_write[p] : w.start_ts = ts
    /\ key_lock' = [key_lock EXCEPT ![p] = {x \in @ : x.ts # ts}]
    /\ key_write' = [key_write EXCEPT ![p] = @ \cup
          {[start_ts |-> ts, commit_ts |-> ts, type |-> "rollback"]}]
    /\ key_data' = [key_data EXCEPT ![p] = @ \ {ts}]
    /\ UNCHANGED <<next_ts, client_state, client_ts, client_read,
                   client_pending, key_last_read_ts>>

Resolve(k) == ResolveCommitted(k) \/ ResolveRolledBack(k) \/ RollbackPrimary(k)

-----------------------------------------------------------------------------
ClientStep(c) ==
  \/ Start(c)
  \/ \E k \in KEY : OptRead(c, k) \/ OptPrewrite(c, k)
                    \/ PessLock(c, k) \/ PessPrewrite(c, k)
                    \/ CommitSecondary(c, k)
  \/ GetCommitTs(c)
  \/ CommitPrimary(c)

Done ==
  /\ \A c \in CLIENT : client_state[c] \in {"committed", "aborted", "crashed"}
                       /\ client_pending[c] = {}
  /\ \A k \in KEY : key_lock[k] = {}

Next ==
  \/ \E c \in CLIENT : ClientStep(c) \/ Crash(c)
  \/ \E k \in KEY : Resolve(k)
  \/ (Done /\ UNCHANGED vars)

Fairness ==
  /\ \A c \in CLIENT : WF_vars(ClientStep(c))
  /\ \A k \in KEY : WF_vars(Resolve(k))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)
TypeOK ==
  /\ next_ts \in Nat
  /\ client_state \in [CLIENT -> States]
  /\ client_ts \in [CLIENT -> TsRec]
  /\ client_read \in [CLIENT -> SUBSET ReadRec]
  /\ client_pending \in [CLIENT -> SUBSET KEY]
  /\ key_lock \in [KEY -> SUBSET LockRec]
  /\ key_write \in [KEY -> SUBSET WriteRec]
  /\ key_data \in [KEY -> SUBSET Nat]
  /\ key_last_read_ts \in [KEY -> Nat]

\* 1. Snapshot isolation: every value read matches the snapshot at the read ts.
SnapshotIsolation ==
  \A c \in CLIENT : \A r \in client_read[c] :
    r.val = LatestWrite(r.key, ReadTs(c))

TxnCommitted(ts) ==
  \E k \in KEY : \E w \in key_write[k] : w.start_ts = ts /\ w.type = "write"
TxnRolledBack(ts) ==
  \E k \in KEY : RolledBack(k, ts)

\* 2. A transaction is never both committed and aborted.
CommitConsistency ==
  \A c \in CLIENT :
    LET ts == client_ts[c].start_ts IN
    /\ ts > 0 => ~ (TxnCommitted(ts) /\ TxnRolledBack(ts))
    /\ client_state[c] = "committed" => ~ TxnRolledBack(ts)
    /\ client_state[c] = "aborted" => ~ TxnCommitted(ts)

\* 3. Committed writes are durable: each key is committed or still holds a
\*    prewrite lock that will be rolled forward.
NoLostUpdate ==
  \A c \in CLIENT :
    client_state[c] = "committed" =>
      \A k \in CLIENT_KEY[c] :
        \/ \E w \in key_write[k] :
             /\ w.start_ts = client_ts[c].start_ts
             /\ w.type = "write"
             /\ w.commit_ts = client_ts[c].commit_ts
        \/ \E l \in key_lock[k] :
             l.ts = client_ts[c].start_ts /\ l.type = "prewrite"

\* 4. At most one lock per key.
LockSafety == \A k \in KEY : Cardinality(key_lock[k]) <= 1

\* 5. Commit timestamps respect start, for_update and min_commit constraints.
TimestampOrder ==
  /\ \A k \in KEY : \A w \in key_write[k] :
       w.type = "write" => w.commit_ts > w.start_ts
  /\ \A c \in CLIENT :
       client_ts[c].commit_ts > 0 =>
         /\ client_ts[c].commit_ts > client_ts[c].start_ts
         /\ client_ts[c].commit_ts >= client_ts[c].min_commit_ts
         /\ c \in PESSIMISTIC_CLIENT =>
              client_ts[c].commit_ts > client_ts[c].for_update_ts
  /\ \A c \in CLIENT :
       client_state[c] = "committed" =>
         \A k \in KEY : \A w \in key_write[k] :
           (w.start_ts = client_ts[c].start_ts /\ w.type = "write")
             => w.commit_ts = client_ts[c].commit_ts

Safety ==
  /\ TypeOK
  /\ SnapshotIsolation
  /\ CommitConsistency
  /\ NoLostUpdate
  /\ LockSafety
  /\ TimestampOrder

THEOREM Spec => []Safety

-----------------------------------------------------------------------------
(* Liveness properties *)
Termination ==
  <>(\A c \in CLIENT : client_state[c] \in {"committed", "aborted", "crashed"})

LocksEventuallyResolved == <>[](\A k \in KEY : key_lock[k] = {})

THEOREM Spec => Termination /\ LocksEventuallyResolved
=============================================================================
```