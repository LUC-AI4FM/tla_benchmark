```tla
 : CLIENT, key : KEY, start_ts : Ts, commit_ts : Ts]
  \cup [type : {"check_txn_status"}, key : KEY, start_ts : Ts, resolving_key : KEY]
  \cup [type : {"resolve_committed"}, key : KEY, start_ts : Ts, commit_ts : Ts]
  \cup [type : {"resolve_rollbacked"}, key : KEY, start_ts : Ts]

SendReqs(msgs) == req_msgs' = req_msgs \cup msgs

----------------------------------------------------------------------------------------
Init ==
  /\ next_ts = 1
  /\ client_state = [c \in CLIENT |-> "init"]
  /\ client_ts = [c \in CLIENT |-> [start_ts |-> NoneTs, commit_ts |-> NoneTs,
                                    for_update_ts |-> NoneTs]]
  /\ client_key = [c \in CLIENT |-> [locking |-> {}, prewriting |-> {}]]
  /\ key_lock = [k \in KEY |-> {}]
  /\ key_write = [k \in KEY |-> {}]
  /\ key_data = [k \in KEY |-> {}]
  /\ req_msgs = {}

----------------------------------------------------------------------------------------
\* Client-side response handling (responses are modeled as atomic client updates).

ClientOnLockOk(c, k) ==
  IF client_state[c] = "locking" /\ k \in client_key[c].locking
  THEN IF client_key[c].locking = {k}
       THEN /\ client_state' = [client_state EXCEPT ![c] = "prewriting"]
            /\ client_key' = [client_key EXCEPT ![c] =
                                [locking |-> {}, prewriting |-> CLIENT_KEY[c]]]
            /\ SendReqs({[type |-> "prewrite_pessimistic", client |-> c, key |-> kk,
                          start_ts |-> client_ts[c].start_ts,
                          primary |-> CLIENT_PRIMARY[c]] : kk \in CLIENT_KEY[c]})
            /\ UNCHANGED <<client_ts, next_ts>>
       ELSE /\ client_key' = [client_key EXCEPT ![c].locking = @ \ {k}]
            /\ UNCHANGED <<client_state, client_ts, next_ts, req_msgs>>
  ELSE UNCHANGED <<client_state, client_ts, client_key, next_ts, req_msgs>>

ClientOnPrewriteOk(c, k) ==
  IF client_state[c] = "prewriting" /\ k \in client_key[c].prewriting
  THEN IF client_key[c].prewriting = {k}
       THEN /\ client_state' = [client_state EXCEPT ![c] = "committing"]
            /\ client_ts' = [client_ts EXCEPT ![c].commit_ts = next_ts]
            /\ next_ts' = next_ts + 1
            /\ client_key' = [client_key EXCEPT ![c].prewriting = {}]
            /\ SendReqs({[type |-> "commit", client |-> c, key |-> CLIENT_PRIMARY[c],
                          start_ts |-> client_ts[c].start_ts, commit_ts |-> next_ts]})
       ELSE /\ client_key' = [client_key EXCEPT ![c].prewriting = @ \ {k}]
            /\ UNCHANGED <<client_state, client_ts, next_ts, req_msgs>>
  ELSE UNCHANGED <<client_state, client_ts, client_key, next_ts, req_msgs>>

ClientOnFail(c) ==
  IF client_state[c] \in {"locking", "prewriting"}
  THEN /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
       /\ client_key' = [client_key EXCEPT ![c] = [locking |-> {}, prewriting |-> {}]]
       /\ UNCHANGED client_ts
  ELSE UNCHANGED client_vars

ClientOnCommitOk(c) ==
  IF client_state[c] = "committing"
  THEN /\ client_state' = [client_state EXCEPT ![c] = "committed"]
       /\ SendReqs({[type |-> "resolve_committed", key |-> kk,
                     start_ts |-> client_ts[c].start_ts,
                     commit_ts |-> client_ts[c].commit_ts] : kk \in SecondaryKeys(c)})
       /\ UNCHANGED <<client_ts, client_key, next_ts>>
  ELSE UNCHANGED <<client_state, client_ts, client_key, next_ts, req_msgs>>

ClientOnCommitFail(c) ==
  /\ IF client_state[c] = "committing"
     THEN client_state' = [client_state EXCEPT ![c] = "aborted"]
     ELSE UNCHANGED client_state
  /\ UNCHANGED <<client_ts, client_key, next_ts, req_msgs>>

----------------------------------------------------------------------------------------
\* Client-initiated actions.

ClientLockKey(c) ==
  /\ c \in PESSIMISTIC_CLIENT
  /\ client_state[c] = "init"
  /\ client_state' = [client_state EXCEPT ![c] = "locking"]
  /\ client_ts' = [client_ts EXCEPT ![c] = [start_ts |-> next_ts, commit_ts |-> NoneTs,
                                            for_update_ts |-> next_ts]]
  /\ client_key' = [client_key EXCEPT ![c].locking = CLIENT_KEY[c]]
  /\ next_ts' = next_ts + 1
  /\ SendReqs({[type |-> "lock_key", client |-> c, key |-> kk, start_ts |-> next_ts,
                primary |-> CLIENT_PRIMARY[c], for_update_ts |-> next_ts]
               : kk \in CLIENT_KEY[c]})
  /\ UNCHANGED key_vars

ClientPrewriteOptimistic(c) ==
  /\ c \in OPTIMISTIC_CLIENT
  /\ client_state[c] = "init"
  /\ client_state' = [client_state EXCEPT ![c] = "prewriting"]
  /\ client_ts' = [client_ts EXCEPT ![c].start_ts = next_ts]
  /\ client_key' = [client_key EXCEPT ![c].prewriting = CLIENT_KEY[c]]
  /\ next_ts' = next_ts + 1
  /\ SendReqs({[type |-> "prewrite_optimistic", client |-> c, key |-> kk,
                start_ts |-> next_ts, primary |-> CLIENT_PRIMARY[c]]
               : kk \in CLIENT_KEY[c]})
  /\ UNCHANGED key_vars

----------------------------------------------------------------------------------------
\* Server actions.

CheckMsg(l, k) == [type |-> "check_txn_status", key |-> l.primary,
                   start_ts |-> l.ts, resolving_key |-> k]

ServerLockKey ==
  \E m \in req_msgs :
    /\ m.type = "lock_key"
    /\ LET k == m.key IN
       IF key_lock[k] = {}
       THEN IF \E w \in key_write[k] :
                  (w.type = "write" /\ w.ts > m.for_update_ts) \/ w.start_ts = m.start_ts
            THEN /\ ClientOnFail(m.client)
                 /\ UNCHANGED <<next_ts, req_msgs, key_lock, key_write, key_data>>
            ELSE /\ key_lock' = [key_lock EXCEPT ![k] =
                         {[ts |-> m.start_ts, primary |-> m.primary, type |-> "lock_key"]}]
                 /\ ClientOnLockOk(m.client, k)
                 /\ UNCHANGED <<key_write, key_data>>
       ELSE LET l == CHOOSE x \in key_lock[k] : TRUE IN
            IF l.ts = m.start_ts
            THEN /\ ClientOnLockOk(m.client, k)
                 /\ UNCHANGED key_vars
            ELSE /\ SendReqs({CheckMsg(l, k)})
                 /\ UNCHANGED <<next_ts, client_state, client_ts, client_key,
                                key_lock, key_write, key_data>>

ServerPrewritePessimistic ==
  \E m \in req_msgs :
    /\ m.type = "prewrite_pessimistic"
    /\ LET k == m.key IN
       IF \E l \in key_lock[k] : l.ts = m.start_ts
       THEN /\ key_lock' = [key_lock EXCEPT ![k] =
                    {[ts |-> m.start_ts, primary |-> m.primary, type |-> "prewrite"]}]
            /\ key_data' = [key_data EXCEPT ![k] = @ \cup {m.start_ts}]
            /\ ClientOnPrewriteOk(m.client, k)
            /\ UNCHANGED key_write
       ELSE IF \E w \in key_write[k] : w.start_ts = m.start_ts /\ w.type = "write"
            THEN UNCHANGED vars
            ELSE /\ ClientOnFail(m.client)
                 /\ UNCHANGED <<next_ts, req_msgs, key_lock, key_write, key_data>>

ServerPrewriteOptimistic ==
  \E m \in req_msgs :
    /\ m.type = "prewrite_optimistic"
    /\ LET k == m.key IN
       IF key_lock[k] = {}
       THEN IF \E w \in key_write[k] :
                  (w.type = "write" /\ w.ts >= m.start_ts) \/ w.start_ts = m.start_ts
            THEN /\ ClientOnFail(m.client)
                 /\ UNCHANGED <<next_ts, req_msgs, key_lock, key_write, key_data>>
            ELSE /\ key_lock' = [key_lock EXCEPT ![k] =
                         {[ts |-> m.start_ts, primary |-> m.primary, type |-> "prewrite"]}]
                 /\ key_data' = [key_data EXCEPT ![k] = @ \cup {m.start_ts}]
                 /\ ClientOnPrewriteOk(m.client, k)
                 /\ UNCHANGED key_write
       ELSE LET l == CHOOSE x \in key_lock[k] : TRUE IN
            IF l.ts = m.start_ts
            THEN /\ ClientOnPrewriteOk(m.client, k)
                 /\ UNCHANGED key_vars
            ELSE /\ SendReqs({CheckMsg(l, k)})
                 /\ UNCHANGED <<next_ts, client_state, client_ts, client_key,
                                key_lock, key_write, key_data>>

ServerCommit ==
  \E m \in req_msgs :
    /\ m.type = "commit"
    /\ LET k == m.key IN
       IF \E l \in key_lock[k] : l.ts = m.start_ts
       THEN /\ key_lock' = [key_lock EXCEPT ![k] = {}]
            /\ key_write' = [key_write EXCEPT ![k] = @ \cup
                    {[ts |-> m.commit_ts, start_ts |-> m.start_ts, type |-> "write"]}]
            /\ ClientOnCommitOk(m.client)
            /\ UNCHANGED key_data
       ELSE IF \E w \in key_write[k] : w.start_ts = m.start_ts /\ w.type = "write"
            THEN /\ ClientOnCommitOk(m.client)
                 /\ UNCHANGED key_vars
            ELSE /\ ClientOnCommitFail(m.client)
                 /\ UNCHANGED key_vars

\* TTL is abstracted: any lock checked is considered expired.
ServerCheckTxnStatus ==
  \E m \in req_msgs :
    /\ m.type = "check_txn_status"
    /\ LET k == m.key
           rb == [type |-> "resolve_rollbacked", key |-> m.resolving_key,
                  start_ts |-> m.start_ts]
           rbRec == [ts |-> m.start_ts, start_ts |-> m.start_ts, type |-> "rollback"]
       IN
       IF \E l \in key_lock[k] : l.ts = m.start_ts
       THEN /\ key_lock' = [key_lock EXCEPT ![k] = {}]
            /\ key_write' = [key_write EXCEPT ![k] = @ \cup {rbRec}]
            /\ SendReqs({rb})
            /\ UNCHANGED <<next_ts, client_state, client_ts, client_key, key_data>>
       ELSE IF \E w \in key_write[k] : w.start_ts = m.start_ts
            THEN LET w == CHOOSE x \in key_write[k] : x.start_ts = m.start_ts IN
                 /\ IF w.type = "write"
                    THEN SendReqs({[type |-> "resolve_committed", key |-> m.resolving_key,
                                    start_ts |-> m.start_ts, commit_ts |-> w.ts]})
                    ELSE SendReqs({rb})
                 /\ UNCHANGED <<next_ts, client_state, client_ts, client_key,
                                key_lock, key_write, key_data>>
            ELSE /\ key_write' = [key_write EXCEPT ![k] = @ \cup {rbRec}]
                 /\ SendReqs({rb})
                 /\ UNCHANGED <<next_ts, client_state, client_ts, client_key,
                                key_lock, key_data>>

ServerResolveCommitted ==
  \E m \in req_msgs :
    /\ m.type = "resolve_committed"
    /\ \E l \in key_lock[m.key] :
         /\ l.ts = m.start_ts
         /\ key_lock' = [key_lock EXCEPT ![m.key] = {}]
         /\ IF l.type = "prewrite"
            THEN key_write' = [key_write EXCEPT ![m.key] = @ \cup
                    {[ts |-> m.commit_ts, start_ts |-> m.start_ts, type |-> "write"]}]
            ELSE UNCHANGED key_write
    /\ UNCHANGED <<next_ts, client_state, client_ts, client_key, key_data, req_msgs>>

ServerResolveRollbacked ==
  \E m \in req_msgs :
    /\ m.type = "resolve_rollbacked"
    /\ \E l \in key_lock[m.key] : l.ts = m.start_ts
    /\ key_lock' = [key_lock EXCEPT ![m.key] = {}]
    /\ key_write' = [key_write EXCEPT ![m.key] = @ \cup
            {[ts |-> m.start_ts, start_ts |-> m.start_ts, type |-> "rollback"]}]
    /\ UNCHANGED <<next_ts, client_state, client_ts, client_key, key_data, req_msgs>>

----------------------------------------------------------------------------------------
Next ==
  \/ \E c \in CLIENT : ClientLockKey(c) \/ ClientPrewriteOptimistic(c)
  \/ ServerLockKey
  \/ ServerPrewritePessimistic
  \/ ServerPrewriteOptimistic
  \/ ServerCommit
  \/ ServerCheckTxnStatus
  \/ ServerResolveCommitted
  \/ ServerResolveRollbacked

Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------------------
\* Safety invariants.

TypeOK ==
  /\ next_ts \in Nat
  /\ client_state \in [CLIENT -> {"init", "locking", "prewriting", "committing",
                                  "committed", "aborted"}]
  /\ client_ts \in [CLIENT -> [start_ts : Ts, commit_ts : Ts, for_update_ts : Ts]]
  /\ client_key \in [CLIENT -> [locking : SUBSET KEY, prewriting : SUBSET KEY]]
  /\ DOMAIN key_lock = KEY /\ \A k \in KEY : key_lock[k] \subseteq Lock
  /\ DOMAIN key_write = KEY /\ \A k \in KEY : key_write[k] \subseteq WriteRec
  /\ DOMAIN key_data = KEY /\ \A k \in KEY : key_data[k] \subseteq Ts
  /\ req_msgs \subseteq ReqMessages

CommitConsistency ==
  \A c \in CLIENT : client_state[c] = "committed" =>
    LET st == client_ts[c].start_ts
        ct == client_ts[c].commit_ts
    IN /\ \E w \in key_write[CLIENT_PRIMARY[c]] :
            w.start_ts = st /\ w.ts = ct /\ w.type = "write"
       /\ \A k \in CLIENT_KEY[c] :
            \/ \E l \in key_lock[k] : l.ts = st /\ l.type = "prewrite"
            \/ \E w \in key_write[k] : w.start_ts = st /\ w.ts = ct /\ w.type = "write"

AbortConsistency ==
  \A c \in CLIENT : client_state[c] = "aborted" =>
    \A k \in CLIENT_KEY[c] :
      ~ \E w \in key_write[k] : w.start_ts = client_ts[c].start_ts /\ w.type = "write"

LockWriteConsistency ==
  \A k \in KEY :
    /\ \A l \in key_lock[k] : ~ \E w \in key_write[k] : w.start_ts = l.ts
    /\ \A l \in key_lock[k] : l.type = "prewrite" => l.ts \in key_data[k]
    /\ \A w \in key_write[k] : w.type = "write" => w.start_ts \in key_data[k]

UniqueLockPerKey == \A k \in KEY : Cardinality(key_lock[k]) <= 1

UniqueWrite ==
  \A k \in KEY : \A w1, w2 \in key_write[k] :
    (w1.ts = w2.ts \/ w1.start_ts = w2.start_ts) => w1 = w2

Started(c) == client_state[c] # "init"

UniqueTimestamp ==
  \A c1, c2 \in CLIENT :
    (c1 # c2 /\ Started(c1) /\ Started(c2)) =>
      /\ client_ts[c1].start_ts # client_ts[c2].start_ts
      /\ client_ts[c1].commit_ts # NoneTs =>
            client_ts[c1].commit_ts \notin {client_ts[c2].start_ts, client_ts[c2].commit_ts}

MsgTsConsistency ==
  \A m \in req_msgs :
    /\ m.start_ts < next_ts
    /\ m.type \in {"commit", "resolve_committed"} =>
          m.start_ts < m.commit_ts /\ m.commit_ts < next_ts
    /\ m.type = "lock_key" => m.start_ts <= m.for_update_ts

ClientOf(ts) == CHOOSE c \in CLIENT : Started(c) /\ client_ts[c].start_ts = ts

CommittedWrites(k) == {w \in key_write[k] : w.type = "write"}

OptimisticSnapshotIsolation ==
  \A k \in KEY : \A w1, w2 \in CommittedWrites(k) :
    (w1 # w2 /\ ClientOf(w2.start_ts) \in OPTIMISTIC_CLIENT) =>
      ~ (w2.start_ts < w1.ts /\ w1.ts < w2.ts)

PessimisticSnapshotIsolation ==
  \A k \in KEY : \A w1, w2 \in CommittedWrites(k) :
    (w1 # w2 /\ ClientOf(w2.start_ts) \in PESSIMISTIC_CLIENT) =>
      ~ (client_ts[ClientOf(w2.start_ts)].for_update_ts < w1.ts /\ w1.ts < w2.ts)

Safety ==
  /\ TypeOK
  /\ CommitConsistency
  /\ AbortConsistency
  /\ LockWriteConsistency
  /\ UniqueLockPerKey
  /\ UniqueWrite
  /\ UniqueTimestamp
  /\ MsgTsConsistency
  /\ OptimisticSnapshotIsolation
  /\ PessimisticSnapshotIsolation

THEOREM Spec => []Safety
========================================================================================
```