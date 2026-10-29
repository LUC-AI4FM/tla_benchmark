```tla
ending = KeysOf(c)]
  /\ UNCHANGED <<next_ts, client_ts, key_lock, key_data, key_write,
                 key_last_read_ts, key_read>>

\* Prewrite a key: primary and secondaries may be locked in any order.
Prewrite(c, k) ==
  LET ts == client_ts[c].start_ts
      conflict == \/ key_lock[k] /= {}
                  \/ \E w \in key_write[k] :
                        \/ w.start_ts = ts
                        \/ (w.type = "write" /\ w.ts >= ts)
  IN
  /\ client_state[c] = "prewriting"
  /\ k \in client_key[c].pending
  /\ IF conflict
       THEN /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
            /\ client_key' = [client_key EXCEPT ![c].pending = {}]
            /\ UNCHANGED <<client_ts, key_lock, key_data>>
       ELSE /\ key_lock' = [key_lock EXCEPT ![k] = @ \cup {LockOf(c)}]
            /\ key_data' = [key_data EXCEPT ![k] = @ \cup {ts}]
            /\ client_ts' = [client_ts EXCEPT ![c].commit_ts =
                                Max(@, key_last_read_ts[k])]
            /\ client_key' = [client_key EXCEPT ![c].pending = @ \ {k}]
            /\ client_state' = [client_state EXCEPT ![c] =
                                 IF client_key[c].pending = {k}
                                   THEN "prewrote" ELSE "prewriting"]
  /\ UNCHANGED <<next_ts, key_write, key_last_read_ts, key_read>>

\* Commit the primary key; commit ts is incremented past all observed reads.
CommitPrimary(c) ==
  LET p == client_key[c].primary
      newCommit == client_ts[c].commit_ts + 1
  IN
  /\ client_state[c] = "prewrote"
  /\ IF LockOf(c) \in key_lock[p]
       THEN /\ client_ts' = [client_ts EXCEPT ![c].commit_ts = newCommit]
            /\ key_lock' = [key_lock EXCEPT ![p] = @ \ {LockOf(c)}]
            /\ key_write' = [key_write EXCEPT ![p] = @ \cup
                              {[ts |-> newCommit,
                                start_ts |-> client_ts[c].start_ts,
                                type |-> "write"]}]
            /\ client_state' = [client_state EXCEPT ![c] = "committed"]
            /\ client_key' = [client_key EXCEPT ![c].pending = client_key[c].secondary]
            /\ next_ts' = Max(next_ts, newCommit)
       ELSE /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
            /\ client_key' = [client_key EXCEPT ![c].pending = {}]
            /\ UNCHANGED <<client_ts, key_lock, key_write, next_ts>>
  /\ UNCHANGED <<key_data, key_last_read_ts, key_read>>

\* Asynchronously commit a secondary key.
CommitSecondary(c, k) ==
  /\ client_state[c] = "committed"
  /\ k \in client_key[c].pending
  /\ IF LockOf(c) \in key_lock[k]
       THEN /\ key_lock' = [key_lock EXCEPT ![k] = @ \ {LockOf(c)}]
            /\ key_write' = [key_write EXCEPT ![k] = @ \cup {WriteOf(c)}]
       ELSE UNCHANGED <<key_lock, key_write>>
  /\ client_key' = [client_key EXCEPT ![c].pending = @ \ {k}]
  /\ UNCHANGED <<next_ts, client_state, client_ts, key_data,
                 key_last_read_ts, key_read>>

\* Roll back the transaction with start ts "ts" at key k.
RollbackKey(k, ts) ==
  /\ key_lock' = [key_lock EXCEPT ![k] = {x \in @ : x.ts /= ts}]
  /\ key_data' = [key_data EXCEPT ![k] = @ \ {ts}]
  /\ key_write' = [key_write EXCEPT ![k] = @ \cup {RollbackRec(ts)}]

\* Clean up a (possibly stale) lock of another transaction.
Cleanup(c, k, l) ==
  /\ client_state[c] \in {"working", "prewriting"}
  /\ k \in KeysOf(c)
  /\ l \in key_lock[k]
  /\ l.ts /= client_ts[c].start_ts
  /\ IF l.primary = k
       THEN RollbackKey(k, l.ts)
       ELSE
         LET p == l.primary IN
         IF \E w \in key_write[p] : w.start_ts = l.ts /\ w.type = "write"
           THEN LET w == CHOOSE x \in key_write[p] :
                           x.start_ts = l.ts /\ x.type = "write"
                IN /\ key_lock' = [key_lock EXCEPT ![k] = @ \ {l}]
                   /\ key_write' = [key_write EXCEPT ![k] = @ \cup
                                     {[ts |-> w.ts, start_ts |-> l.ts,
                                       type |-> "write"]}]
                   /\ UNCHANGED key_data
           ELSE IF \E w \in key_write[p] : w.start_ts = l.ts /\ w.type = "rollback"
             THEN RollbackKey(k, l.ts)
             ELSE RollbackKey(p, l.ts)
  /\ UNCHANGED <<next_ts, client_state, client_ts, client_key,
                 key_last_read_ts, key_read>>

Done ==
  /\ \A c \in CLIENT : client_state[c] \in {"committed", "aborted"}
                       /\ client_key[c].pending = {}
  /\ UNCHANGED vars

Next ==
  \/ \E c \in CLIENT :
       \/ Start(c)
       \/ FinishRead(c)
       \/ CommitPrimary(c)
       \/ \E k \in KEY :
            \/ ReadKey(c, k)
            \/ Prewrite(c, k)
            \/ CommitSecondary(c, k)
            \/ \E l \in key_lock[k] : Cleanup(c, k, l)
  \/ Done

PercolatorSpec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

TypeInvariant ==
  /\ next_ts \in Nat
  /\ client_state \in [CLIENT -> States]
  /\ \A c \in CLIENT : client_ts[c].start_ts \in Nat /\ client_ts[c].commit_ts \in Nat
  /\ client_key \in [CLIENT -> [primary : KEY, secondary : SUBSET KEY,
                                pending : SUBSET KEY]]
  /\ \A k \in KEY :
       /\ \A l \in key_lock[k] : l \in [ts : Nat, primary : KEY]
       /\ \A d \in key_data[k] : d \in Nat
       /\ \A w \in key_write[k] :
            w \in [ts : Nat, start_ts : Nat, type : {"write", "rollback"}]
       /\ key_last_read_ts[k] \in Nat

WriteConsistency ==
  \A k \in KEY :
    LET W == {w \in key_write[k] : w.type = "write"} IN
    /\ \A w \in W : w.ts > w.start_ts
    /\ \A w1, w2 \in W :
         w1 /= w2 => (w1.ts < w2.start_ts \/ w2.ts < w1.start_ts)

LockConsistency ==
  /\ \A k \in KEY : Cardinality(key_lock[k]) <= 1
  /\ \A c \in CLIENT :
       (client_state[c] = "prewrote" /\ LockOf(c) \in key_lock[client_key[c].primary])
         => \A s \in client_key[c].secondary : LockOf(c) \in key_lock[s]

CommittedConsistency ==
  \A c \in CLIENT :
    client_state[c] = "committed" =>
      /\ WriteOf(c) \in key_write[client_key[c].primary]
      /\ LockOf(c) \notin key_lock[client_key[c].primary]
      /\ \A s \in client_key[c].secondary :
           \/ LockOf(c) \in key_lock[s] /\ WriteOf(c) \notin key_write[s]
           \/ LockOf(c) \notin key_lock[s] /\ WriteOf(c) \in key_write[s]

AbortedConsistency ==
  \A c \in CLIENT :
    client_state[c] = "aborted" =>
      ~\E w \in key_write[client_key[c].primary] :
          w.start_ts = client_ts[c].start_ts /\ w.type = "write"

RollbackConsistency ==
  \A c \in CLIENT :
    client_state[c] /= "init" =>
      ~(/\ \E k \in KeysOf(c) : \E w \in key_write[k] :
             w.start_ts = client_ts[c].start_ts /\ w.type = "write"
        /\ \E k \in KeysOf(c) : \E w \in key_write[k] :
             w.start_ts = client_ts[c].start_ts /\ w.type = "rollback")

UniqueWrite ==
  \A k \in KEY : \A w \in key_write[k] :
    Cardinality({x \in key_write[k] : x.start_ts = w.start_ts}) = 1

SnapshotIsolation ==
  \A k \in KEY : \A r \in key_read[k] :
    {w \in key_write[k] : w.type = "write" /\ w.ts <= r.ts} = r.seen

=============================================================================
```