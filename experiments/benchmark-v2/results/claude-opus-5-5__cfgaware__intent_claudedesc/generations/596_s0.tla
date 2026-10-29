---------------------------- MODULE DistributedTransaction ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS k1, k2, c1, c2,
          KEY, OPTIMISTIC_CLIENT, PESSIMISTIC_CLIENT,
          CLIENT_READ_KEY, CLIENT_WRITE_KEY, CLIENT_PRIMARY

\* Concrete scenario: two keys, one optimistic and one pessimistic client
Keys == {k1, k2}
OptimistiicClient == {c1}
PessimisticClient == {c2}
ClientReadKeys == [c \in {c1, c2} |-> {k1, k2}]
ClientWriteKeys == [c \in {c1, c2} |-> {k1, k2}]
ClientPrimary == [c \in {c1, c2} |-> IF c = c1 THEN k1 ELSE k2]

CLIENT == OPTIMISTIC_CLIENT \cup PESSIMISTIC_CLIENT

VARIABLES next_ts, client_state, client_ts, client_key, client_read,
          key_lock, key_write, key_data, msgs

vars == <<next_ts, client_state, client_ts, client_key, client_read,
          key_lock, key_write, key_data, msgs>>

ClientStates == {"init", "working", "committing", "committed", "aborted"}

\* start_ts of the latest committed version with commit ts < ts (0 = initial value)
LatestBefore(k, ts) ==
  LET W == {w \in key_write[k] : w.type = "write" /\ w.ts < ts}
  IN IF W = {} THEN 0
     ELSE (CHOOSE w \in W : \A w2 \in W : w2.ts <= w.ts).start_ts

\* Some lock with ts <= start blocks a snapshot read at start
ReadBlocked(k, ts) == \E l \in key_lock[k] : l.ts <= ts

\* A committed write at or after start conflicts
WriteConflict(k, ts) == \E w \in key_write[k] : w.type = "write" /\ w.ts >= ts

Init ==
  /\ next_ts = 1
  /\ client_state = [c \in CLIENT |-> "init"]
  /\ client_ts = [c \in CLIENT |-> [start_ts |-> 0, commit_ts |-> 0]]
  /\ client_key = [c \in CLIENT |-> [reading |-> {}, locking |-> {}, prewriting |-> {}]]
  /\ client_read = [c \in CLIENT |-> [k \in KEY |-> 0]]
  /\ key_lock = [k \in KEY |-> {}]
  /\ key_write = [k \in KEY |-> {}]
  /\ key_data = [k \in KEY |-> {}]
  /\ msgs = {}

ClientStart(c) ==
  /\ client_state[c] = "init"
  /\ client_state' = [client_state EXCEPT ![c] = "working"]
  /\ client_ts' = [client_ts EXCEPT ![c].start_ts = next_ts]
  /\ next_ts' = next_ts + 1
  /\ client_key' = [client_key EXCEPT ![c] =
        IF c \in PESSIMISTIC_CLIENT
        THEN [reading |-> CLIENT_READ_KEY[c] \ CLIENT_WRITE_KEY[c],
              locking |-> CLIENT_WRITE_KEY[c],
              prewriting |-> CLIENT_WRITE_KEY[c]]
        ELSE [reading |-> CLIENT_READ_KEY[c],
              locking |-> {},
              prewriting |-> CLIENT_WRITE_KEY[c]]]
  /\ UNCHANGED <<client_read, key_lock, key_write, key_data, msgs>>

\* Snapshot read (optimistic reads; pessimistic read-only keys)
ClientReadKey(c, k) ==
  LET s == client_ts[c].start_ts IN
  /\ client_state[c] = "working"
  /\ k \in client_key[c].reading
  /\ ~ReadBlocked(k, s)
  /\ client_read' = [client_read EXCEPT ![c][k] = LatestBefore(k, s)]
  /\ client_key' = [client_key EXCEPT ![c].reading = @ \ {k}]
  /\ UNCHANGED <<next_ts, client_state, client_ts, key_lock, key_write, key_data, msgs>>

\* Pessimistic lock acquisition, reading the locked value
ClientLockKey(c, k) ==
  LET s == client_ts[c].start_ts IN
  /\ c \in PESSIMISTIC_CLIENT
  /\ client_state[c] = "working"
  /\ k \in client_key[c].locking
  /\ key_lock[k] = {}
  /\ ~WriteConflict(k, s)
  /\ key_lock' = [key_lock EXCEPT ![k] =
        {[ts |-> s, primary |-> CLIENT_PRIMARY[c], type |-> "lock"]}]
  /\ client_read' = IF k \in CLIENT_READ_KEY[c]
                    THEN [client_read EXCEPT ![c][k] = LatestBefore(k, s)]
                    ELSE client_read
  /\ client_key' = [client_key EXCEPT ![c].locking = @ \ {k}]
  /\ UNCHANGED <<next_ts, client_state, client_ts, key_write, key_data, msgs>>

ClientPrewrite(c, k) ==
  LET s == client_ts[c].start_ts
      newLock == [ts |-> s, primary |-> CLIENT_PRIMARY[c], type |-> "prewrite"]
  IN
  /\ client_state[c] = "working"
  /\ client_key[c].reading = {}
  /\ client_key[c].locking = {}
  /\ k \in client_key[c].prewriting
  /\ IF c \in PESSIMISTIC_CLIENT
     THEN key_lock[k] = {[ts |-> s, primary |-> CLIENT_PRIMARY[c], type |-> "lock"]}
     ELSE key_lock[k] = {} /\ ~WriteConflict(k, s)
  /\ key_lock' = [key_lock EXCEPT ![k] = {newLock}]
  /\ key_data' = [key_data EXCEPT ![k] = @ \cup {s}]
  /\ client_key' = [client_key EXCEPT ![c].prewriting = @ \ {k}]
  /\ UNCHANGED <<next_ts, client_state, client_ts, client_read, key_write, msgs>>

ClientGetCommitTs(c) ==
  LET s == client_ts[c].start_ts IN
  /\ client_state[c] = "working"
  /\ client_key[c].reading = {}
  /\ client_key[c].locking = {}
  /\ client_key[c].prewriting = {}
  /\ \A k \in CLIENT_WRITE_KEY[c] :
        \E l \in key_lock[k] : l.ts = s /\ l.type = "prewrite"
  /\ client_state' = [client_state EXCEPT ![c] = "committing"]
  /\ client_ts' = [client_ts EXCEPT ![c].commit_ts = next_ts]
  /\ next_ts' = next_ts + 1
  /\ UNCHANGED <<client_key, client_read, key_lock, key_write, key_data, msgs>>

ClientCommitPrimary(c) ==
  LET s == client_ts[c].start_ts
      t == client_ts[c].commit_ts
      p == CLIENT_PRIMARY[c]
  IN
  /\ client_state[c] = "committing"
  /\ \E l \in key_lock[p] : l.ts = s /\ l.type = "prewrite"
  /\ key_lock' = [key_lock EXCEPT ![p] = {l \in @ : l.ts # s}]
  /\ key_write' = [key_write EXCEPT ![p] =
        @ \cup {[ts |-> t, start_ts |-> s, type |-> "write"]}]
  /\ client_state' = [client_state EXCEPT ![c] = "committed"]
  /\ msgs' = msgs \cup {[c |-> c, start_ts |-> s, commit_ts |-> t]}
  /\ UNCHANGED <<next_ts, client_ts, client_key, client_read, key_data>>

ServerCommitSecondary(m, k) ==
  /\ k \in CLIENT_WRITE_KEY[m.c]
  /\ \E l \in key_lock[k] : l.ts = m.start_ts /\ l.type = "prewrite"
  /\ key_lock' = [key_lock EXCEPT ![k] = {l \in @ : l.ts # m.start_ts}]
  /\ key_write' = [key_write EXCEPT ![k] =
        @ \cup {[ts |-> m.commit_ts, start_ts |-> m.start_ts, type |-> "write"]}]
  /\ UNCHANGED <<next_ts, client_state, client_ts, client_key, client_read, key_data, msgs>>

ClientAbort(c) ==
  LET s == client_ts[c].start_ts
      p == CLIENT_PRIMARY[c]
  IN
  /\ client_state[c] = "working"
  /\ key_lock' = [k \in KEY |-> {l \in key_lock[k] : l.ts # s}]
  /\ key_data' = [k \in KEY |-> key_data[k] \ {s}]
  /\ key_write' = [key_write EXCEPT ![p] =
        @ \cup {[ts |-> s, start_ts |-> s, type |-> "rollback"]}]
  /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
  /\ UNCHANGED <<next_ts, client_ts, client_key, client_read, msgs>>

Next ==
  \/ \E c \in CLIENT :
       \/ ClientStart(c)
       \/ ClientGetCommitTs(c)
       \/ ClientCommitPrimary(c)
       \/ ClientAbort(c)
       \/ \E k \in KEY : ClientReadKey(c, k) \/ ClientLockKey(c, k) \/ ClientPrewrite(c, k)
  \/ \E m \in msgs, k \in KEY : ServerCommitSecondary(m, k)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Invariants

TypeOK ==
  /\ next_ts \in Nat
  /\ \A c \in CLIENT :
       /\ client_state[c] \in ClientStates
       /\ client_ts[c].start_ts \in Nat
       /\ client_ts[c].commit_ts \in Nat
       /\ client_key[c].reading \subseteq KEY
       /\ client_key[c].locking \subseteq KEY
       /\ client_key[c].prewriting \subseteq KEY
       /\ \A k \in KEY : client_read[c][k] \in Nat
  /\ \A k \in KEY :
       /\ \A l \in key_lock[k] :
            l.ts \in Nat /\ l.primary \in KEY /\ l.type \in {"lock", "prewrite"}
       /\ \A w \in key_write[k] :
            w.ts \in Nat /\ w.start_ts \in Nat /\ w.type \in {"write", "rollback"}
       /\ key_data[k] \subseteq Nat
  /\ \A m \in msgs :
       m.c \in CLIENT /\ m.start_ts \in Nat /\ m.commit_ts \in Nat

UniqueCommitOrAbort ==
  \A k \in KEY : \A w1, w2 \in key_write[k] :
     w1.start_ts = w2.start_ts => w1 = w2

CommitConsistency ==
  \A c \in CLIENT : client_state[c] = "committed" =>
     LET s == client_ts[c].start_ts
         t == client_ts[c].commit_ts
     IN /\ s < t
        /\ \E w \in key_write[CLIENT_PRIMARY[c]] :
              w.start_ts = s /\ w.ts = t /\ w.type = "write"
        /\ \A k \in CLIENT_WRITE_KEY[c] :
              /\ s \in key_data[k]
              /\ \/ \E w \in key_write[k] :
                       w.start_ts = s /\ w.ts = t /\ w.type = "write"
                 \/ \E l \in key_lock[k] : l.ts = s /\ l.type = "prewrite"

AbortConsistency ==
  \A c \in CLIENT : client_state[c] = "aborted" =>
     LET s == client_ts[c].start_ts IN
     \A k \in KEY :
        /\ ~\E w \in key_write[k] : w.start_ts = s /\ w.type = "write"
        /\ ~\E l \in key_lock[k] : l.ts = s
        /\ s \notin key_data[k]

WriteConsistency ==
  \A k \in KEY : \A w1, w2 \in key_write[k] :
     (w1 # w2 /\ w1.type = "write" /\ w2.type = "write") =>
        (w1.ts < w2.start_ts \/ w2.ts < w1.start_ts)

UniqueLockOrWrite ==
  \A k \in KEY :
     /\ Cardinality(key_lock[k]) <= 1
     /\ \A l \in key_lock[k], w \in key_write[k] : l.ts # w.start_ts

UniqueWrite ==
  \A k \in KEY : \A w1, w2 \in key_write[k] :
     w1.ts = w2.ts => w1 = w2

OptimisticReadSnapshotIsolation ==
  \A c \in OPTIMISTIC_CLIENT : client_state[c] = "committed" =>
     \A k \in CLIENT_READ_KEY[c] :
        client_read[c][k] = LatestBefore(k, client_ts[c].start_ts)

PessimisticReadSnapshotIsolation ==
  \A c \in PESSIMISTIC_CLIENT : client_state[c] = "committed" =>
     \A k \in CLIENT_READ_KEY[c] :
        client_read[c][k] = LatestBefore(k, client_ts[c].start_ts)

MsgTsConsistency ==
  \A m \in msgs :
     /\ m.start_ts < m.commit_ts
     /\ m.commit_ts < next_ts
     /\ client_ts[m.c].start_ts = m.start_ts
     /\ client_ts[m.c].commit_ts = m.commit_ts
     /\ client_state[m.c] = "committed"

=============================================================================