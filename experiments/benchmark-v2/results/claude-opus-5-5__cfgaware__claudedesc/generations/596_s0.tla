---- MODULE MC ----
EXTENDS Integers, FiniteSets, Sequences, TLC

\* Model values
CONSTANTS k1, k2, c1, c2

\* Parameters of the DistributedTransaction protocol
CONSTANTS KEY, OPTIMISTIC_CLIENT, PESSIMISTIC_CLIENT,
          CLIENT_READ_KEY, CLIENT_WRITE_KEY, CLIENT_PRIMARY

\* Concrete definitions substituted for the constants by the configuration
Keys == {k1, k2}
OptimistiicClient == {c2}
PessimisticClient == {c1}
ClientReadKeys == [c \in {c1, c2} |-> IF c = c1 THEN {} ELSE {k1, k2}]
ClientWriteKeys == [c \in {c1, c2} |-> {k1, k2}]
ClientPrimary == [c \in {c1, c2} |-> k1]

-----------------------------------------------------------------------------
\* Generic DistributedTransaction protocol (Percolator-style)

CLIENT == PESSIMISTIC_CLIENT \cup OPTIMISTIC_CLIENT
NoneTs == 0
NoRead == -1

ClientStates == {"init", "locking", "reading", "prewriting",
                 "committing", "committed", "aborted"}
LockTypes == {"lock_key", "prewrite_optimistic", "prewrite_pessimistic"}
WriteTypes == {"write", "rollback"}
ReqTypes == {"lock_key", "prewrite_optimistic", "prewrite_pessimistic",
             "commit", "resolve_committed", "resolve_rollbacked"}
RespTypes == {"locked_key", "lock_key_failed", "prewrited",
              "prewrite_failed", "committed", "commit_failed"}
FailTypes == {"lock_key_failed", "prewrite_failed", "commit_failed"}

VARIABLES next_ts, client_state, client_ts, client_key, client_read,
          key_lock, key_write, key_data, req_msgs, resp_msgs

vars == <<next_ts, client_state, client_ts, client_key, client_read,
          key_lock, key_write, key_data, req_msgs, resp_msgs>>

WriteSet(k) == {key_write[k][i] : i \in DOMAIN key_write[k]}

LatestCommitBefore(k, ts) ==
  LET W == {w \in WriteSet(k) : w.type = "write" /\ w.ts <= ts}
  IN IF W = {} THEN NoneTs
     ELSE (CHOOSE w \in W : \A w2 \in W : w2.ts <= w.ts).start_ts

HasLock(k, ts) == \E l \in key_lock[k] : l.ts = ts
HasRecord(k, ts) == \E w \in WriteSet(k) : w.start_ts = ts
HasCommit(k, ts) == \E w \in WriteSet(k) : w.start_ts = ts /\ w.type = "write"

Resp(m, t, v) == [c |-> m.c, type |-> t, key |-> m.key,
                  start_ts |-> m.start_ts, value |-> v]

Init ==
  /\ next_ts = 1
  /\ client_state = [c \in CLIENT |-> "init"]
  /\ client_ts = [c \in CLIENT |-> [start_ts |-> NoneTs, commit_ts |-> NoneTs,
                                     for_update_ts |-> NoneTs]]
  /\ client_key = [c \in CLIENT |-> [locking |-> {}, prewriting |-> {}]]
  /\ client_read = [c \in CLIENT |-> [k \in KEY |-> NoRead]]
  /\ key_lock = [k \in KEY |-> {}]
  /\ key_write = [k \in KEY |-> <<>>]
  /\ key_data = [k \in KEY |-> {}]
  /\ req_msgs = {}
  /\ resp_msgs = {}

-----------------------------------------------------------------------------
\* Client actions

ClientLockKey(c) ==
  /\ c \in PESSIMISTIC_CLIENT
  /\ client_state[c] = "init"
  /\ client_state' = [client_state EXCEPT ![c] = "locking"]
  /\ client_ts' = [client_ts EXCEPT ![c].start_ts = next_ts,
                                    ![c].for_update_ts = next_ts]
  /\ next_ts' = next_ts + 1
  /\ client_key' = [client_key EXCEPT ![c].locking = CLIENT_WRITE_KEY[c]]
  /\ req_msgs' = req_msgs \cup
       {[c |-> c, type |-> "lock_key", key |-> k, start_ts |-> next_ts,
         primary |-> CLIENT_PRIMARY[c], for_update_ts |-> next_ts]
         : k \in CLIENT_WRITE_KEY[c]}
  /\ UNCHANGED <<client_read, key_lock, key_write, key_data, resp_msgs>>

ClientLockedKey(c) ==
  /\ client_state[c] = "locking"
  /\ \E m \in resp_msgs :
       /\ m.c = c
       /\ m.type = "locked_key"
       /\ m.key \in client_key[c].locking
       /\ client_key' = [client_key EXCEPT ![c].locking = @ \ {m.key}]
       /\ client_read' = IF m.key \in CLIENT_READ_KEY[c]
                           THEN [client_read EXCEPT ![c][m.key] = m.value]
                           ELSE client_read
       /\ resp_msgs' = resp_msgs \ {m}
  /\ UNCHANGED <<next_ts, client_state, client_ts, key_lock, key_write,
                 key_data, req_msgs>>

ClientPrewritePessimistic(c) ==
  /\ client_state[c] = "locking"
  /\ client_key[c].locking = {}
  /\ client_state' = [client_state EXCEPT ![c] = "prewriting"]
  /\ client_key' = [client_key EXCEPT ![c].prewriting = CLIENT_WRITE_KEY[c]]
  /\ req_msgs' = req_msgs \cup
       {[c |-> c, type |-> "prewrite_pessimistic", key |-> k,
         start_ts |-> client_ts[c].start_ts, primary |-> CLIENT_PRIMARY[c]]
         : k \in CLIENT_WRITE_KEY[c]}
  /\ UNCHANGED <<next_ts, client_ts, client_read, key_lock, key_write,
                 key_data, resp_msgs>>

ClientStartOptimistic(c) ==
  /\ c \in OPTIMISTIC_CLIENT
  /\ client_state[c] = "init"
  /\ client_state' = [client_state EXCEPT ![c] = "reading"]
  /\ client_ts' = [client_ts EXCEPT ![c].start_ts = next_ts]
  /\ next_ts' = next_ts + 1
  /\ UNCHANGED <<client_key, client_read, key_lock, key_write, key_data,
                 req_msgs, resp_msgs>>

ClientReadKey(c) ==
  /\ client_state[c] = "reading"
  /\ \E k \in CLIENT_READ_KEY[c] :
       /\ client_read[c][k] = NoRead
       /\ ~\E l \in key_lock[k] :
              l.ts <= client_ts[c].start_ts /\ l.type # "lock_key"
       /\ client_read' = [client_read EXCEPT ![c][k] =
                            LatestCommitBefore(k, client_ts[c].start_ts)]
  /\ UNCHANGED <<next_ts, client_state, client_ts, client_key, key_lock,
                 key_write, key_data, req_msgs, resp_msgs>>

ClientPrewriteOptimistic(c) ==
  /\ client_state[c] = "reading"
  /\ \A k \in CLIENT_READ_KEY[c] : client_read[c][k] # NoRead
  /\ client_state' = [client_state EXCEPT ![c] = "prewriting"]
  /\ client_key' = [client_key EXCEPT ![c].prewriting = CLIENT_WRITE_KEY[c]]
  /\ req_msgs' = req_msgs \cup
       {[c |-> c, type |-> "prewrite_optimistic", key |-> k,
         start_ts |-> client_ts[c].start_ts, primary |-> CLIENT_PRIMARY[c]]
         : k \in CLIENT_WRITE_KEY[c]}
  /\ UNCHANGED <<next_ts, client_ts, client_read, key_lock, key_write,
                 key_data, resp_msgs>>

ClientPrewrited(c) ==
  /\ client_state[c] = "prewriting"
  /\ \E m \in resp_msgs :
       /\ m.c = c
       /\ m.type = "prewrited"
       /\ m.key \in client_key[c].prewriting
       /\ client_key' = [client_key EXCEPT ![c].prewriting = @ \ {m.key}]
       /\ resp_msgs' = resp_msgs \ {m}
  /\ UNCHANGED <<next_ts, client_state, client_ts, client_read, key_lock,
                 key_write, key_data, req_msgs>>

ClientCommit(c) ==
  /\ client_state[c] = "prewriting"
  /\ client_key[c].prewriting = {}
  /\ client_state' = [client_state EXCEPT ![c] = "committing"]
  /\ client_ts' = [client_ts EXCEPT ![c].commit_ts = next_ts]
  /\ next_ts' = next_ts + 1
  /\ req_msgs' = req_msgs \cup
       {[c |-> c, type |-> "commit", key |-> CLIENT_PRIMARY[c],
         start_ts |-> client_ts[c].start_ts, commit_ts |-> next_ts]}
  /\ UNCHANGED <<client_key, client_read, key_lock, key_write, key_data,
                 resp_msgs>>

ClientCommitted(c) ==
  /\ client_state[c] = "committing"
  /\ \E m \in resp_msgs :
       /\ m.c = c
       /\ m.type = "committed"
       /\ resp_msgs' = resp_msgs \ {m}
  /\ client_state' = [client_state EXCEPT ![c] = "committed"]
  /\ req_msgs' = req_msgs \cup
       {[type |-> "resolve_committed", start_ts |-> client_ts[c].start_ts,
         commit_ts |-> client_ts[c].commit_ts]}
  /\ UNCHANGED <<next_ts, client_ts, client_key, client_read, key_lock,
                 key_write, key_data>>

ClientAbort(c) ==
  /\ client_state[c] \in {"locking", "prewriting", "committing"}
  /\ \E m \in resp_msgs :
       /\ m.c = c
       /\ m.type \in FailTypes
       /\ resp_msgs' = resp_msgs \ {m}
  /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
  /\ req_msgs' = req_msgs \cup
       {[type |-> "resolve_rollbacked", start_ts |-> client_ts[c].start_ts]}
  /\ UNCHANGED <<next_ts, client_ts, client_key, client_read, key_lock,
                 key_write, key_data>>

-----------------------------------------------------------------------------
\* Server actions

ServerLockKey ==
  \E m \in req_msgs :
    /\ m.type = "lock_key"
    /\ req_msgs' = req_msgs \ {m}
    /\ LET k == m.key IN
       IF HasLock(k, m.start_ts)
       THEN /\ resp_msgs' = resp_msgs \cup
                 {Resp(m, "locked_key", LatestCommitBefore(k, m.for_update_ts))}
            /\ UNCHANGED key_lock
       ELSE IF \/ key_lock[k] # {}
               \/ \E w \in WriteSet(k) :
                     \/ w.start_ts = m.start_ts
                     \/ (w.type = "write" /\ w.ts > m.for_update_ts)
       THEN /\ resp_msgs' = resp_msgs \cup {Resp(m, "lock_key_failed", NoRead)}
            /\ UNCHANGED key_lock
       ELSE /\ key_lock' = [key_lock EXCEPT ![k] = @ \cup
                 {[ts |-> m.start_ts, primary |-> m.primary,
                   type |-> "lock_key", for_update_ts |-> m.for_update_ts]}]
            /\ resp_msgs' = resp_msgs \cup
                 {Resp(m, "locked_key", LatestCommitBefore(k, m.for_update_ts))}
    /\ UNCHANGED <<next_ts, client_state, client_ts, client_key, client_read,
                   key_write, key_data>>

ServerPrewritePessimistic ==
  \E m \in req_msgs :
    /\ m.type = "prewrite_pessimistic"
    /\ req_msgs' = req_msgs \ {m}
    /\ LET k == m.key IN
       IF HasLock(k, m.start_ts)
       THEN /\ key_lock' = [key_lock EXCEPT ![k] =
                 {IF l.ts = m.start_ts
                    THEN [l EXCEPT !.type = "prewrite_pessimistic"]
                    ELSE l : l \in @}]
            /\ key_data' = [key_data EXCEPT ![k] = @ \cup {m.start_ts}]
            /\ resp_msgs' = resp_msgs \cup {Resp(m, "prewrited", NoRead)}
       ELSE /\ resp_msgs' = resp_msgs \cup {Resp(m, "prewrite_failed", NoRead)}
            /\ UNCHANGED <<key_lock, key_data>>
    /\ UNCHANGED <<next_ts, client_state, client_ts, client_key, client_read,
                   key_write>>

ServerPrewriteOptimistic ==
  \E m \in req_msgs :
    /\ m.type = "prewrite_optimistic"
    /\ req_msgs' = req_msgs \ {m}
    /\ LET k == m.key IN
       IF HasLock(k, m.start_ts)
       THEN /\ resp_msgs' = resp_msgs \cup {Resp(m, "prewrited", NoRead)}
            /\ UNCHANGED <<key_lock, key_data>>
       ELSE IF \/ key_lock[k] # {}
               \/ \E w \in WriteSet(k) :
                     \/ w.start_ts = m.start_ts
                     \/ (w.type = "write" /\ w.ts > m.start_ts)
       THEN /\ resp_msgs' = resp_msgs \cup {Resp(m, "prewrite_failed", NoRead)}
            /\ UNCHANGED <<key_lock, key_data>>
       ELSE /\ key_lock' = [key_lock EXCEPT ![k] = @ \cup
                 {[ts |-> m.start_ts, primary |-> m.primary,
                   type |-> "prewrite_optimistic", for_update_ts |-> NoneTs]}]
            /\ key_data' = [key_data EXCEPT ![k] = @ \cup {m.start_ts}]
            /\ resp_msgs' = resp_msgs \cup {Resp(m, "prewrited", NoRead)}
    /\ UNCHANGED <<next_ts, client_state, client_ts, client_key, client_read,
                   key_write>>

ServerCommit ==
  \E m \in req_msgs :
    /\ m.type = "commit"
    /\ req_msgs' = req_msgs \ {m}
    /\ LET k == m.key IN
       IF \E l \in key_lock[k] : l.ts = m.start_ts /\ l.type # "lock_key"
       THEN /\ key_lock' = [key_lock EXCEPT ![k] =
                 {l \in @ : l.ts # m.start_ts}]
            /\ key_write' = [key_write EXCEPT ![k] = Append(@,
                 [ts |-> m.commit_ts, start_ts |-> m.start_ts, type |-> "write"])]
            /\ resp_msgs' = resp_msgs \cup {Resp(m, "committed", NoRead)}
       ELSE IF HasCommit(k, m.start_ts)
       THEN /\ resp_msgs' = resp_msgs \cup {Resp(m, "committed", NoRead)}
            /\ UNCHANGED <<key_lock, key_write>>
       ELSE /\ resp_msgs' = resp_msgs \cup {Resp(m, "commit_failed", NoRead)}
            /\ UNCHANGED <<key_lock, key_write>>
    /\ UNCHANGED <<next_ts, client_state, client_ts, client_key, client_read,
                   key_data>>

ServerResolveCommitted ==
  \E m \in req_msgs :
    /\ m.type = "resolve_committed"
    /\ req_msgs' = req_msgs \ {m}
    /\ key_write' = [k \in KEY |->
         IF \E l \in key_lock[k] : l.ts = m.start_ts /\ l.type # "lock_key"
           THEN Append(key_write[k],
                  [ts |-> m.commit_ts, start_ts |-> m.start_ts, type |-> "write"])
           ELSE key_write[k]]
    /\ key_lock' = [k \in KEY |-> {l \in key_lock[k] : l.ts # m.start_ts}]
    /\ UNCHANGED <<next_ts, client_state, client_ts, client_key, client_read,
                   key_data, resp_msgs>>

ServerResolveRollbacked ==
  \E m \in req_msgs :
    /\ m.type = "resolve_rollbacked"
    /\ req_msgs' = req_msgs \ {m}
    /\ key_lock' = [k \in KEY |-> {l \in key_lock[k] : l.ts # m.start_ts}]
    /\ key_data' = [k \in KEY |->
         IF HasCommit(k, m.start_ts) THEN key_data[k]
         ELSE key_data[k] \ {m.start_ts}]
    /\ key_write' = [k \in KEY |->
         IF HasRecord(k, m.start_ts) THEN key_write[k]
         ELSE Append(key_write[k],
                [ts |-> m.start_ts, start_ts |-> m.start_ts, type |-> "rollback"])]
    /\ UNCHANGED <<next_ts, client_state, client_ts, client_key, client_read,
                   resp_msgs>>

\* Another party finds a stale primary lock and rolls the transaction back.
ServerCleanupStaleLock ==
  \E k \in KEY :
    \E l \in key_lock[k] :
      /\ l.primary = k
      /\ key_lock' = [key_lock EXCEPT ![k] = @ \ {l}]
      /\ key_data' = [key_data EXCEPT ![k] = @ \ {l.ts}]
      /\ key_write' = [key_write EXCEPT ![k] = Append(@,
           [ts |-> l.ts, start_ts |-> l.ts, type |-> "rollback"])]
      /\ req_msgs' = req_msgs \cup
           {[type |-> "resolve_rollbacked", start_ts |-> l.ts]}
      /\ UNCHANGED <<next_ts, client_state, client_ts, client_key,
                     client_read, resp_msgs>>

Done ==
  /\ \A c \in CLIENT : client_state[c] \in {"committed", "aborted"}
  /\ UNCHANGED vars

Next ==
  \/ \E c \in CLIENT :
       \/ ClientLockKey(c)
       \/ ClientLockedKey(c)
       \/ ClientPrewritePessimistic(c)
       \/ ClientStartOptimistic(c)
       \/ ClientReadKey(c)
       \/ ClientPrewriteOptimistic(c)
       \/ ClientPrewrited(c)
       \/ ClientCommit(c)
       \/ ClientCommitted(c)
       \/ ClientAbort(c)
  \/ ServerLockKey
  \/ ServerPrewritePessimistic
  \/ ServerPrewriteOptimistic
  \/ ServerCommit
  \/ ServerResolveCommitted
  \/ ServerResolveRollbacked
  \/ ServerCleanupStaleLock
  \/ Done

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Invariants

TypeOK ==
  /\ next_ts \in Nat
  /\ client_state \in [CLIENT -> ClientStates]
  /\ \A c \in CLIENT :
       /\ client_ts[c].start_ts \in Nat
       /\ client_ts[c].commit_ts \in Nat
       /\ client_ts[c].for_update_ts \in Nat
       /\ client_key[c].locking \subseteq KEY
       /\ client_key[c].prewriting \subseteq KEY
       /\ \A k \in KEY : client_read[c][k] \in Nat \cup {NoRead}
  /\ \A k \in KEY :
       /\ \A l \in key_lock[k] :
            /\ l.ts \in Nat
            /\ l.primary \in KEY
            /\ l.type \in LockTypes
            /\ l.for_update_ts \in Nat
       /\ \A w \in WriteSet(k) :
            /\ w.ts \in Nat
            /\ w.start_ts \in Nat
            /\ w.type \in WriteTypes
       /\ key_data[k] \subseteq Nat
  /\ \A m \in req_msgs : m.type \in ReqTypes
  /\ \A m \in resp_msgs : m.type \in RespTypes /\ m.c \in CLIENT

UniqueCommitOrAbort ==
  \A c \in CLIENT :
    LET ts == client_ts[c].start_ts IN
      ~ /\ \E k \in KEY : \E w \in WriteSet(k) :
              w.start_ts = ts /\ w.type = "write"
        /\ \E k \in KEY : \E w \in WriteSet(k) :
              w.start_ts = ts /\ w.type = "rollback"

CommitConsistency ==
  \A c \in CLIENT :
    client_state[c] = "committed" =>
      \E w \in WriteSet(CLIENT_PRIMARY[c]) :
        /\ w.type = "write"
        /\ w.start_ts = client_ts[c].start_ts
        /\ w.ts = client_ts[c].commit_ts

AbortConsistency ==
  \A c \in CLIENT :
    client_state[c] = "aborted" =>
      ~HasCommit(CLIENT_PRIMARY[c], client_ts[c].start_ts)

WriteConsistency ==
  \A k \in KEY : \A w \in WriteSet(k) :
    w.type = "write" =>
      /\ w.start_ts \in key_data[k]
      /\ w.ts > w.start_ts

UniqueLockOrWrite ==
  \A k \in KEY :
    /\ Cardinality(key_lock[k]) <= 1
    /\ \A l \in key_lock[k] : ~HasRecord(k, l.ts)

UniqueWrite ==
  \A k \in KEY :
    \A i, j \in DOMAIN key_write[k] :
      i # j =>
        /\ key_write[k][i].start_ts # key_write[k][j].start_ts
        /\ (key_write[k][i].type = "write" /\ key_write[k][j].type = "write")
             => key_write[k][i].ts # key_write[k][j].ts

OptimisticReadSnapshotIsolation ==
  \A c \in OPTIMISTIC_CLIENT : \A k \in CLIENT_READ_KEY[c] :
    client_read[c][k] # NoRead =>
      client_read[c][k] = LatestCommitBefore(k, client_ts[c].start_ts)

PessimisticReadSnapshotIsolation ==
  \A c \in PESSIMISTIC_CLIENT : \A k \in CLIENT_READ_KEY[c] :
    client_read[c][k] # NoRead =>
      client_read[c][k] = LatestCommitBefore(k, client_ts[c].for_update_ts)

MsgTsConsistency ==
  \A m \in req_msgs \cup resp_msgs :
    /\ m.start_ts < next_ts
    /\ ("commit_ts" \in DOMAIN m) =>
         (m.commit_ts < next_ts /\ m.commit_ts > m.start_ts)
    /\ ("for_update_ts" \in DOMAIN m) =>
         (m.for_update_ts < next_ts /\ m.for_update_ts >= m.start_ts)

=============================================================================