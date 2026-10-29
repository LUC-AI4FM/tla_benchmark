}]

LockKeyMsg     == [type : {"lock_key"}, key : KEY, primary : KEY,
                   start_ts : Nat, for_update_ts : Nat]
PrewriteOptMsg == [type : {"prewrite_optimistic"}, key : KEY, primary : KEY,
                   start_ts : Nat]
PrewritePesMsg == [type : {"prewrite_pessimistic"}, key : KEY, primary : KEY,
                   start_ts : Nat, for_update_ts : Nat]
CommitMsg      == [type : {"commit"}, primary : KEY, start_ts : Nat, commit_ts : Nat]
CheckMsg       == [type : {"check_txn_status"}, primary : KEY, start_ts : Nat]
ResolveCMsg    == [type : {"resolve_committed"}, start_ts : Nat, commit_ts : Nat]
ResolveRMsg    == [type : {"resolve_rollbacked"}, start_ts : Nat]

ReqMsg == LockKeyMsg \cup PrewriteOptMsg \cup PrewritePesMsg \cup CommitMsg
            \cup CheckMsg \cup ResolveCMsg \cup ResolveRMsg

-----------------------------------------------------------------------------
(* Helpers *)

SendReqs(ms) == req_msgs' = req_msgs \cup ms

HasLock(k, t)         == \E l \in key_lock[k] : l.ts = t
HasLockOfType(k, t, y) == \E l \in key_lock[k] : l.ts = t /\ l.type = y
HasWriteOf(k, t)      == \E w \in key_write[k] : w.start_ts = t
HasCommitted(k, t)    == \E w \in key_write[k] : w.start_ts = t /\ w.type = "write"
HasRollback(k, t)     == \E w \in key_write[k] : w.start_ts = t /\ w.type = "rollback"
HasCommitAfter(k, t)  == \E w \in key_write[k] : w.type = "write" /\ w.ts > t

RollbackRec(t) == [ts |-> t, start_ts |-> t, type |-> "rollback"]

-----------------------------------------------------------------------------
Init ==
    /\ next_ts = 1
    /\ client_state = [c \in CLIENT |-> "init"]
    /\ client_ts = [c \in CLIENT |-> [start_ts |-> 0, commit_ts |-> 0, for_update_ts |-> 0]]
    /\ key_lock = [k \in KEY |-> {}]
    /\ key_write = [k \in KEY |-> {}]
    /\ key_data = [k \in KEY |-> {}]
    /\ req_msgs = {}

-----------------------------------------------------------------------------
(* Client actions *)

\* Optimistic client gets start_ts and sends prewrites for all its keys.
OptimisticBegin(c) ==
    /\ c \in OPTIMISTIC_CLIENT
    /\ client_state[c] = "init"
    /\ LET s == next_ts IN
         /\ next_ts' = next_ts + 1
         /\ client_ts' = [client_ts EXCEPT ![c].start_ts = s]
         /\ client_state' = [client_state EXCEPT ![c] = "prewriting"]
         /\ SendReqs({[type |-> "prewrite_optimistic", key |-> k,
                       primary |-> CLIENT_PRIMARY[c], start_ts |-> s]
                      : k \in CLIENT_KEY[c]})
    /\ UNCHANGED <<key_lock, key_write, key_data>>

\* Pessimistic client gets start_ts (= initial for_update_ts) and sends lock_key requests.
PessimisticBegin(c) ==
    /\ c \in PESSIMISTIC_CLIENT
    /\ client_state[c] = "init"
    /\ LET s == next_ts IN
         /\ next_ts' = next_ts + 1
         /\ client_ts' = [client_ts EXCEPT ![c].start_ts = s, ![c].for_update_ts = s]
         /\ client_state' = [client_state EXCEPT ![c] = "locking"]
         /\ SendReqs({[type |-> "lock_key", key |-> k, primary |-> CLIENT_PRIMARY[c],
                       start_ts |-> s, for_update_ts |-> s]
                      : k \in CLIENT_KEY[c]})
    /\ UNCHANGED <<key_lock, key_write, key_data>>

\* Pessimistic client hit a write conflict while locking: retry with a new for_update_ts.
PessimisticRetryLock(c) ==
    /\ c \in PESSIMISTIC_CLIENT
    /\ client_state[c] = "locking"
    /\ LET s == client_ts[c].start_ts
           f == client_ts[c].for_update_ts
       IN /\ \E k \in CLIENT_KEY[c] : ~HasLock(k, s) /\ HasCommitAfter(k, f)
          /\ next_ts' = next_ts + 1
          /\ client_ts' = [client_ts EXCEPT ![c].for_update_ts = next_ts]
          /\ SendReqs({[type |-> "lock_key", key |-> k, primary |-> CLIENT_PRIMARY[c],
                        start_ts |-> s, for_update_ts |-> next_ts]
                       : k \in CLIENT_KEY[c]})
    /\ UNCHANGED <<client_state, key_lock, key_write, key_data>>

\* Pessimistic client observes all its keys locked; sends pessimistic prewrites.
PessimisticLocked(c) ==
    /\ c \in PESSIMISTIC_CLIENT
    /\ client_state[c] = "locking"
    /\ LET s == client_ts[c].start_ts IN
         /\ \A k \in CLIENT_KEY[c] : HasLockOfType(k, s, "pessimistic")
         /\ client_state' = [client_state EXCEPT ![c] = "prewriting"]
         /\ SendReqs({[type |-> "prewrite_pessimistic", key |-> k,
                       primary |-> CLIENT_PRIMARY[c], start_ts |-> s,
                       for_update_ts |-> client_ts[c].for_update_ts]
                      : k \in CLIENT_KEY[c]})
    /\ UNCHANGED <<next_ts, client_ts, key_lock, key_write, key_data>>

\* All keys prewritten: obtain commit_ts and send commit for the primary.
ClientPrewrited(c) ==
    /\ client_state[c] = "prewriting"
    /\ LET s == client_ts[c].start_ts IN
         /\ \A k \in CLIENT_KEY[c] : HasLockOfType(k, s, "prewrite")
         /\ next_ts' = next_ts + 1
         /\ client_ts' = [client_ts EXCEPT ![c].commit_ts = next_ts]
         /\ client_state' = [client_state EXCEPT ![c] = "committing"]
         /\ SendReqs({[type |-> "commit", primary |-> CLIENT_PRIMARY[c],
                       start_ts |-> s, commit_ts |-> next_ts]})
    /\ UNCHANGED <<key_lock, key_write, key_data>>

\* Primary committed: transaction committed; secondaries resolved asynchronously.
ClientCommitted(c) ==
    /\ client_state[c] = "committing"
    /\ HasCommitted(CLIENT_PRIMARY[c], client_ts[c].start_ts)
    /\ client_state' = [client_state EXCEPT ![c] = "committed"]
    /\ SendReqs({[type |-> "resolve_committed", start_ts |-> client_ts[c].start_ts,
                  commit_ts |-> client_ts[c].commit_ts]})
    /\ UNCHANGED <<next_ts, client_ts, key_lock, key_write, key_data>>

\* Client aborts on rollback or (optimistic) write conflict, and cleans up its locks.
ClientAbort(c) ==
    /\ client_state[c] \in {"locking", "prewriting", "committing"}
    /\ LET s == client_ts[c].start_ts IN
         /\ \/ HasRollback(CLIENT_PRIMARY[c], s)
            \/ /\ client_state[c] \in {"locking", "prewriting"}
               /\ \E k \in CLIENT_KEY[c] : HasRollback(k, s)
            \/ /\ c \in OPTIMISTIC_CLIENT
               /\ client_state[c] = "prewriting"
               /\ \E k \in CLIENT_KEY[c] : ~HasLock(k, s) /\ HasCommitAfter(k, s)
            \/ /\ c \in PESSIMISTIC_CLIENT
               /\ client_state[c] = "locking"
               /\ \E k \in CLIENT_KEY[c] :
                    ~HasLock(k, s) /\ HasCommitAfter(k, client_ts[c].for_update_ts)
         /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
         /\ SendReqs({[type |-> "check_txn_status", primary |-> CLIENT_PRIMARY[c],
                       start_ts |-> s]})
    /\ UNCHANGED <<next_ts, client_ts, key_lock, key_write, key_data>>

\* Client encounters a lock of another transaction and checks its primary's status.
ClientResolveLock(c) ==
    /\ client_state[c] \in {"locking", "prewriting"}
    /\ \E k \in CLIENT_KEY[c] : \E l \in key_lock[k] :
         LET m == [type |-> "check_txn_status", primary |-> l.primary, start_ts |-> l.ts]
         IN /\ l.ts /= client_ts[c].start_ts
            /\ m \notin req_msgs
            /\ SendReqs({m})
    /\ UNCHANGED <<next_ts, client_state, client_ts, key_lock, key_write, key_data>>

-----------------------------------------------------------------------------
(* Server actions *)

ServerLockKey ==
    \E m \in req_msgs :
      /\ m.type = "lock_key"
      /\ key_lock[m.key] = {}
      /\ ~HasWriteOf(m.key, m.start_ts)
      /\ ~HasCommitAfter(m.key, m.for_update_ts)
      /\ key_lock' = [key_lock EXCEPT ![m.key] =
                        {[ts |-> m.start_ts, primary |-> m.primary,
                          type |-> "pessimistic", for_update_ts |-> m.for_update_ts]}]
      /\ UNCHANGED <<next_ts, client_state, client_ts, key_write, key_data, req_msgs>>

ServerPrewriteOptimistic ==
    \E m \in req_msgs :
      /\ m.type = "prewrite_optimistic"
      /\ key_lock[m.key] = {}
      /\ ~HasWriteOf(m.key, m.start_ts)
      /\ ~HasCommitAfter(m.key, m.start_ts)
      /\ key_lock' = [key_lock EXCEPT ![m.key] =
                        {[ts |-> m.start_ts, primary |-> m.primary,
                          type |-> "prewrite", for_update_ts |-> 0]}]
      /\ key_data' = [key_data EXCEPT ![m.key] = @ \cup {m.start_ts}]
      /\ UNCHANGED <<next_ts, client_state, client_ts, key_write, req_msgs>>

ServerPrewritePessimistic ==
    \E m \in req_msgs :
      /\ m.type = "prewrite_pessimistic"
      /\ \E l \in key_lock[m.key] :
           /\ l.ts = m.start_ts
           /\ l.type = "pessimistic"
           /\ key_lock' = [key_lock EXCEPT ![m.key] = {[l EXCEPT !.type = "prewrite"]}]
      /\ key_data' = [key_data EXCEPT ![m.key] = @ \cup {m.start_ts}]
      /\ UNCHANGED <<next_ts, client_state, client_ts, key_write, req_msgs>>

\* Commit a prewrite lock of transaction t on key k with commit timestamp ct.
CommitKey(k, t, ct) ==
    /\ HasLockOfType(k, t, "prewrite")
    /\ key_lock' = [key_lock EXCEPT ![k] = {}]
    /\ key_write' = [key_write EXCEPT ![k] =
                       @ \cup {[ts |-> ct, start_ts |-> t, type |-> "write"]}]

ServerCommit ==
    \E m \in req_msgs :
      /\ m.type = "commit"
      /\ CommitKey(m.primary, m.start_ts, m.commit_ts)
      /\ UNCHANGED <<next_ts, client_state, client_ts, key_data, req_msgs>>

ServerResolveCommitted ==
    \E m \in req_msgs :
      /\ m.type = "resolve_committed"
      /\ \E k \in KEY : CommitKey(k, m.start_ts, m.commit_ts)
      /\ UNCHANGED <<next_ts, client_state, client_ts, key_data, req_msgs>>

ServerResolveRollbacked ==
    \E m \in req_msgs :
      /\ m.type = "resolve_rollbacked"
      /\ \E k \in KEY :
           /\ HasLock(k, m.start_ts)
           /\ key_lock' = [key_lock EXCEPT ![k] = {}]
           /\ key_write' = [key_write EXCEPT ![k] = @ \cup {RollbackRec(m.start_ts)}]
      /\ UNCHANGED <<next_ts, client_state, client_ts, key_data, req_msgs>>

\* check_txn_status on the primary; TTL is abstracted as always expired.
ServerCheckTxnStatus ==
    \E m \in req_msgs :
      /\ m.type = "check_txn_status"
      /\ LET p == m.primary
             t == m.start_ts
             rbMsg == [type |-> "resolve_rollbacked", start_ts |-> t]
         IN IF HasCommitted(p, t)
            THEN /\ \E w \in key_write[p] :
                      /\ w.type = "write"
                      /\ w.start_ts = t
                      /\ SendReqs({[type |-> "resolve_committed", start_ts |-> t,
                                    commit_ts |-> w.ts]})
                 /\ UNCHANGED <<key_lock, key_write>>
            ELSE IF HasRollback(p, t)
            THEN /\ SendReqs({rbMsg})
                 /\ UNCHANGED <<key_lock, key_write>>
            ELSE /\ key_lock' = [key_lock EXCEPT ![p] = {l \in @ : l.ts /= t}]
                 /\ key_write' = [key_write EXCEPT ![p] = @ \cup {RollbackRec(t)}]
                 /\ SendReqs({rbMsg})
      /\ UNCHANGED <<next_ts, client_state, client_ts, key_data>>

-----------------------------------------------------------------------------
Next ==
    \/ \E c \in CLIENT :
         \/ OptimisticBegin(c)
         \/ PessimisticBegin(c)
         \/ PessimisticRetryLock(c)
         \/ PessimisticLocked(c)
         \/ ClientPrewrited(c)
         \/ ClientCommitted(c)
         \/ ClientAbort(c)
         \/ ClientResolveLock(c)
    \/ ServerLockKey
    \/ ServerPrewriteOptimistic
    \/ ServerPrewritePessimistic
    \/ ServerCommit
    \/ ServerResolveCommitted
    \/ ServerResolveRollbacked
    \/ ServerCheckTxnStatus

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety invariants *)

TypeOK ==
    /\ next_ts \in Nat \ {0}
    /\ client_state \in [CLIENT -> ClientStates]
    /\ client_ts \in [CLIENT -> [start_ts : Nat, commit_ts : Nat, for_update_ts : Nat]]
    /\ key_lock \in [KEY -> SUBSET Lock]
    /\ key_write \in [KEY -> SUBSET Write]
    /\ key_data \in [KEY -> SUBSET Nat]
    /\ req_msgs \subseteq ReqMsg

\* At most one lock per key.
UniqueLockPerKey == \A k \in KEY : Cardinality(key_lock[k]) <= 1

\* A lock and a write record of the same transaction never coexist on a key.
LockWriteConsistency ==
    \A k \in KEY : \A l \in key_lock[k] : ~HasWriteOf(k, l.ts)

\* Write records on a key have unique timestamps.
UniqueWriteTs ==
    \A k \in KEY : \A w1, w2 \in key_write[k] : w1.ts = w2.ts => w1 = w2

\* At most one write record (commit or rollback) per transaction per key.
UniqueWritePerTxn ==
    \A k \in KEY : \A w1, w2 \in key_write[k] : w1.start_ts = w2.start_ts => w1 = w2

\* A transaction is either committed (with one commit_ts) or rolled back on all keys.
CommitAbortConsistency ==
    \A k1, k2 \in KEY : \A w1 \in key_write[k1], w2 \in key_write[k2] :
        w1.start_ts = w2.start_ts => (w1.type = w2.type /\ w1.ts = w2.ts)

\* Committed data was actually prewritten.
WriteDataConsistency ==
    \A k \in KEY : \A w \in key_write[k] : w.type = "write" => w.start_ts \in key_data[k]

UniqueStartTs ==
    \A c1, c2 \in CLIENT :
        (c1 /= c2 /\ client_ts[c1].start_ts /= 0) =>
            client_ts[c1].start_ts /= client_ts[c2].start_ts

UniqueCommitTs ==
    \A c1, c2 \in CLIENT :
        (c1 /= c2 /\ client_ts[c1].commit_ts /= 0) =>
            client_ts[c1].commit_ts /= client_ts[c2].commit_ts

\* Committed clients: primary committed, no key rolled back, every key committed or prewritten.
CommittedConsistency ==
    \A c \in CLIENT :
        LET s == client_ts[c].start_ts
            ct == client_ts[c].commit_ts
        IN client_state[c] = "committed" =>
             /\ [ts |-> ct, start_ts |-> s, type |-> "write"] \in key_write[CLIENT_PRIMARY[c]]
             /\ \A k \in CLIENT_KEY[c] :
                  /\ ~HasRollback(k, s)
                  /\ \/ HasLockOfType(k, s, "prewrite")
                     \/ [ts |-> ct, start_ts |-> s, type |-> "write"] \in key_write[k]

\* Aborted clients never have committed writes.
AbortedConsistency ==
    \A c \in CLIENT :
        client_state[c] = "aborted" =>
            \A k \in KEY : ~HasCommitted(k, client_ts[c].start_ts)

\* Message timestamps are consistent with the timestamp oracle and clients.
MsgTsConsistency ==
    \A m \in req_msgs :
        /\ 0 < m.start_ts /\ m.start_ts < next_ts
        /\ m.type \in {"commit", "resolve_committed"} =>
              /\ m.start_ts < m.commit_ts
              /\ m.commit_ts < next_ts
              /\ \E c \in CLIENT : /\ client_ts[c].start_ts = m.start_ts
                                   /\ client_ts[c].commit_ts = m.commit_ts
        /\ m.type \in {"lock_key", "prewrite_pessimistic"} =>
              /\ m.start_ts <= m.for_update_ts
              /\ m.for_update_ts < next_ts

\* Snapshot isolation (no write-write conflict) for optimistic transactions.
OptimisticSnapshotIsolation ==
    \A c \in OPTIMISTIC_CLIENT :
        LET s == client_ts[c].start_ts
            ct == client_ts[c].commit_ts
        IN client_state[c] = "committed" =>
             \A k \in CLIENT_KEY[c] : \A w \in key_write[k] :
                 (w.type = "write" /\ w.start_ts /= s) => ~(s < w.ts /\ w.ts < ct)

\* Snapshot isolation for pessimistic transactions, relative to for_update_ts.
PessimisticSnapshotIsolation ==
    \A c \in PESSIMISTIC_CLIENT :
        LET s == client_ts[c].start_ts
            f == client_ts[c].for_update_ts
            ct == client_ts[c].commit_ts
        IN client_state[c] = "committed" =>
             \A k \in CLIENT_KEY[c] : \A w \in key_write[k] :
                 (w.type = "write" /\ w.start_ts /= s) => ~(f < w.ts /\ w.ts < ct)

Safety ==
    /\ TypeOK
    /\ UniqueLockPerKey
    /\ LockWriteConsistency
    /\ UniqueWriteTs
    /\ UniqueWritePerTxn
    /\ CommitAbortConsistency
    /\ WriteDataConsistency
    /\ UniqueStartTs
    /\ UniqueCommitTs
    /\ CommittedConsistency
    /\ AbortedConsistency
    /\ MsgTsConsistency
    /\ OptimisticSnapshotIsolation
    /\ PessimisticSnapshotIsolation

\* Requests only accumulate; next_ts never decreases.
MsgsMonotonic == [][req_msgs \subseteq req_msgs' /\ next_ts <= next_ts']_vars

THEOREM Spec => []Safety
=============================================================================