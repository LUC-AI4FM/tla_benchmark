```tla
_lock[l.primary] :
            /\ p.ts = l.ts
            /\ p.min_commit_ts <= r
            /\ key_lock' = [key_lock EXCEPT ![l.primary] =
                              (@ \ {p}) \cup {[p EXCEPT !.min_commit_ts = r + 1]}]
  /\ UNCHANGED <<next_ts, client_state, client_ts, client_key, client_read,
                 key_write, key_max_read_ts>>

\* Snapshot read at start_ts; records max read ts on the key
Read(c, k) ==
  LET r == client_ts[c].start_ts IN
  /\ client_state[c] = "working"
  /\ client_read[c][k] = NoRead
  /\ BlockingLocks(k, r) = {}
  /\ client_read' = [client_read EXCEPT ![c][k] = LatestVersion(k, r)]
  /\ key_max_read_ts' = [key_max_read_ts EXCEPT ![k] = Max2(@, r)]
  /\ UNCHANGED <<next_ts, client_state, client_ts, client_key, key_lock, key_write>>

Prewrite(c) ==
  /\ client_state[c] = "working"
  /\ client_state' = [client_state EXCEPT ![c] = "prewriting"]
  /\ UNCHANGED <<next_ts, client_ts, client_key, client_read,
                 key_lock, key_write, key_max_read_ts>>

\* Prewrite one key; the primary key must be prewritten first
PrewriteKey(c, k) ==
  LET s == client_ts[c].start_ts
      p == client_key[c].primary
      m == Max2(s + 1, key_max_read_ts[k] + 1)
  IN
  /\ client_state[c] = "prewriting"
  /\ k \in client_key[c].pending
  /\ (k = p \/ p \notin client_key[c].pending)
  /\ IF key_lock[k] # {} \/ \E w \in WriteSet(k) : w.ts >= s
       THEN /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
            /\ UNCHANGED <<client_ts, client_key, key_lock>>
       ELSE /\ key_lock' = [key_lock EXCEPT ![k] =
                              @ \cup {[ts |-> s, primary |-> p, min_commit_ts |-> m]}]
            /\ client_ts' = [client_ts EXCEPT ![c].min_commit_ts = Max2(@, m)]
            /\ client_key' = [client_key EXCEPT ![c].pending = @ \ {k}]
            /\ UNCHANGED client_state
  /\ UNCHANGED <<next_ts, client_read, key_write, key_max_read_ts>>

\* Commit the primary: commit_ts is derived from min_commit_ts values
Commit(c) ==
  LET s == client_ts[c].start_ts
      p == client_key[c].primary
  IN
  /\ client_state[c] = "prewriting"
  /\ client_key[c].pending = {}
  /\ IF \E l \in key_lock[p] : l.ts = s
       THEN LET l   == CHOOSE x \in key_lock[p] : x.ts = s
                cts == Max2(client_ts[c].min_commit_ts, l.min_commit_ts)
            IN
            /\ key_lock' = [key_lock EXCEPT ![p] = @ \ {l}]
            /\ key_write' = [key_write EXCEPT ![p] =
                               Append(@, [ts |-> cts, start_ts |-> s, type |-> "write"])]
            /\ client_state' = [client_state EXCEPT ![c] = "committed"]
            /\ client_ts' = [client_ts EXCEPT ![c].commit_ts = cts]
       ELSE /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
            /\ UNCHANGED <<key_lock, key_write, client_ts>>
  /\ UNCHANGED <<next_ts, client_key, client_read, key_max_read_ts>>

CommitSecondary(k) ==
  /\ \E l \in key_lock[k] :
       /\ l.primary # k
       /\ PrimaryCommitted(l)
       /\ key_lock' = [key_lock EXCEPT ![k] = @ \ {l}]
       /\ key_write' = [key_write EXCEPT ![k] =
             Append(@, [ts |-> PrimaryCommitTs(l), start_ts |-> l.ts, type |-> "write"])]
  /\ UNCHANGED <<next_ts, client_state, client_ts, client_key, client_read,
                 key_max_read_ts>>

\* Primary lock may be rolled back at any time (e.g. TTL expiry / crash)
RollbackPrimary(k) ==
  /\ \E l \in key_lock[k] :
       /\ l.primary = k
       /\ key_lock' = [key_lock EXCEPT ![k] = @ \ {l}]
       /\ key_write' = [key_write EXCEPT ![k] =
             Append(@, [ts |-> l.ts, start_ts |-> l.ts, type |-> "rollback"])]
  /\ UNCHANGED <<next_ts, client_state, client_ts, client_key, client_read,
                 key_max_read_ts>>

RollbackSecondary(k) ==
  /\ \E l \in key_lock[k] :
       /\ l.primary # k
       /\ PrimaryRolledBack(l)
       /\ key_lock' = [key_lock EXCEPT ![k] = @ \ {l}]
       /\ key_write' = [key_write EXCEPT ![k] =
             Append(@, [ts |-> l.ts, start_ts |-> l.ts, type |-> "rollback"])]
  /\ UNCHANGED <<next_ts, client_state, client_ts, client_key, client_read,
                 key_max_read_ts>>

Done ==
  /\ \A c \in CLIENT : client_state[c] \in {"committed", "aborted"}
  /\ \A k \in KEY : key_lock[k] = {}
  /\ UNCHANGED vars

Next ==
  \/ \E c \in CLIENT :
       \/ Start(c)
       \/ Prewrite(c)
       \/ Commit(c)
       \/ \E k \in KEY : ReadPush(c, k) \/ Read(c, k) \/ PrewriteKey(c, k)
  \/ \E k \in KEY : CommitSecondary(k) \/ RollbackPrimary(k) \/ RollbackSecondary(k)
  \/ Done

PercolatorSpec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
TypeInvariant ==
  /\ next_ts \in Nat
  /\ client_state \in [CLIENT -> {"init", "working", "prewriting", "committed", "aborted"}]
  /\ client_ts \in [CLIENT -> [start_ts : Nat, commit_ts : Nat, min_commit_ts : Nat]]
  /\ client_key \in [CLIENT -> [primary : KEY, secondary : SUBSET KEY, pending : SUBSET KEY]]
  /\ client_read \in [CLIENT -> [KEY -> Nat \cup {NoRead}]]
  /\ key_lock \in [KEY -> SUBSET [ts : Nat, primary : KEY, min_commit_ts : Nat]]
  /\ key_write \in [KEY -> Seq([ts : Nat, start_ts : Nat, type : {"write", "rollback"}])]
  /\ key_max_read_ts \in [KEY -> Nat]

\* Write records on each key are strictly ordered by timestamp
WriteConsistency ==
  \A k \in KEY :
    /\ \A i \in 1..(Len(key_write[k]) - 1) : key_write[k][i].ts < key_write[k][i + 1].ts
    /\ \A w \in WriteSet(k) : w.type = "write" => w.ts > w.start_ts

LockConsistency ==
  /\ \A k \in KEY : Cardinality(key_lock[k]) <= 1
  /\ \A k \in KEY : \A l \in key_lock[k] :
       l.primary # k =>
         \/ \E p \in key_lock[l.primary] : p.ts = l.ts
         \/ \E w \in WriteSet(l.primary) : w.start_ts = l.ts
  /\ \A c \in CLIENT : client_state[c] \in {"init", "working"} =>
       \A k \in KEY : \A l \in key_lock[k] : l.ts # client_ts[c].start_ts

CommittedConsistency ==
  \A c \in CLIENT : client_state[c] = "committed" =>
    LET s == client_ts[c].start_ts
        t == client_ts[c].commit_ts
        p == client_key[c].primary
    IN
    /\ t > s
    /\ \E w \in WriteSet(p) : w.start_ts = s /\ w.type = "write" /\ w.ts = t
    /\ \A k \in client_key[c].secondary :
         \/ \E l \in key_lock[k] : l.ts = s
         \/ \E w \in WriteSet(k) : w.start_ts = s /\ w.type = "write" /\ w.ts = t
    /\ \A k \in KEY : ~ \E w \in WriteSet(k) : w.start_ts = s /\ w.type = "rollback"

AbortedConsistency ==
  \A c \in CLIENT : client_state[c] = "aborted" =>
    \A k \in KEY : ~ \E w \in WriteSet(k) :
       w.start_ts = client_ts[c].start_ts /\ w.type = "write"

RollbackConsistency ==
  \A k \in KEY : \A w \in WriteSet(k) : w.type = "rollback" =>
    /\ \A k2 \in KEY : ~ \E w2 \in WriteSet(k2) :
         w2.start_ts = w.start_ts /\ w2.type = "write"
    /\ \A c \in CLIENT :
         (client_ts[c].start_ts = w.start_ts) => client_state[c] # "committed"

UniqueWrite ==
  \A k \in KEY : \A i, j \in DOMAIN key_write[k] :
    i # j => /\ key_write[k][i].start_ts # key_write[k][j].start_ts
             /\ key_write[k][i].ts # key_write[k][j].ts

SnapshotIsolation ==
  \* No write-write overlap: no committed version lies within another's (start, commit]
  /\ \A k \in KEY : \A v1, v2 \in CommittedVersions(k) :
       v1 # v2 => ~ (v1.start < v2.commit /\ v2.commit < v1.commit)
  \* Every snapshot read stays the latest committed version at its start_ts
  /\ \A c \in CLIENT : \A k \in KEY :
       client_read[c][k] # NoRead =>
         client_read[c][k] = LatestVersion(k, client_ts[c].start_ts)

=============================================================================
```