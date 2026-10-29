--------------------------- MODULE OptimizedCommitTS ---------------------------
EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS KEY, CLIENT, CLIENT_PRIMARY_KEY

ASSUME KEY # {}
ASSUME CLIENT_PRIMARY_KEY \in [CLIENT -> KEY]

VARIABLES next_ts,
          client_state,
          client_ts,
          client_key,
          key_data,
          key_lock,
          key_write,
          key_last_read_ts,
          key_si

client_vars == <<client_state, client_ts, client_key>>
key_vars    == <<key_data, key_lock, key_write, key_last_read_ts, key_si>>
vars        == <<next_ts, client_vars, key_vars>>

Max(a, b) == IF a >= b THEN a ELSE b

Range(s) == {s[i] : i \in DOMAIN s}

ClientStates == {"init", "working", "prewriting", "committing", "committed", "aborted"}

LockRec  == [ts : Nat, primary : KEY]
WriteRec == [start_ts : Nat, commit_ts : Nat, type : {"write", "rollback"}]

ClientKeys(c) == {client_key[c].primary} \cup client_key[c].secondary

HasCommitRecord(k, ts) ==
  \E w \in Range(key_write[k]) : w.type = "write" /\ w.start_ts = ts

HasRollbackRecord(k, ts) ==
  \E w \in Range(key_write[k]) : w.type = "rollback" /\ w.start_ts = ts

HasAnyRecord(k, ts) ==
  \E w \in Range(key_write[k]) : w.start_ts = ts

-----------------------------------------------------------------------------
Init ==
  /\ next_ts = 1
  /\ client_state = [c \in CLIENT |-> "init"]
  /\ client_ts = [c \in CLIENT |-> [start_ts |-> 0, commit_ts |-> 0]]
  /\ client_key = [c \in CLIENT |->
                     [primary   |-> CLIENT_PRIMARY_KEY[c],
                      secondary |-> KEY \ {CLIENT_PRIMARY_KEY[c]},
                      pending   |-> {}]]
  /\ key_data = [k \in KEY |-> {}]
  /\ key_lock = [k \in KEY |-> {}]
  /\ key_write = [k \in KEY |-> <<>>]
  /\ key_last_read_ts = [k \in KEY |-> 0]
  /\ key_si = [k \in KEY |-> TRUE]

-----------------------------------------------------------------------------
\* Start: obtain a start timestamp.
Start(c) ==
  /\ client_state[c] = "init"
  /\ client_state' = [client_state EXCEPT ![c] = "working"]
  /\ client_ts' = [client_ts EXCEPT ![c].start_ts = next_ts]
  /\ next_ts' = next_ts + 1
  /\ UNCHANGED <<client_key, key_vars>>

\* Read key k at start_ts if not blocked by a lock; record last read ts.
ReadKey(c, k) ==
  LET ts == client_ts[c].start_ts IN
  /\ ~ \E l \in key_lock[k] : l.ts <= ts
  /\ key_last_read_ts' = [key_last_read_ts EXCEPT ![k] = Max(@, ts)]
  /\ UNCHANGED <<next_ts, client_vars, key_data, key_lock, key_write, key_si>>

\* Finish reading; move to prewriting phase with all keys pending.
StartPrewrite(c) ==
  /\ client_state' = [client_state EXCEPT ![c] = "prewriting"]
  /\ client_key' = [client_key EXCEPT ![c].pending = ClientKeys(c)]
  /\ UNCHANGED <<next_ts, client_ts, key_vars>>

\* Clean up a (possibly stale) lock on key k encountered while reading.
CleanupLock(c, k) ==
  \E l \in key_lock[k] :
    LET ts == l.ts
        p  == l.primary
    IN
    /\ ts <= client_ts[c].start_ts
    /\ IF \E w \in Range(key_write[p]) : w.type = "write" /\ w.start_ts = ts
       THEN \* Primary committed: roll forward this key.
            LET w == CHOOSE w \in Range(key_write[p]) :
                       w.type = "write" /\ w.start_ts = ts
            IN
            /\ key_lock' = [key_lock EXCEPT ![k] = {x \in @ : x.ts # ts}]
            /\ key_write' = [key_write EXCEPT ![k] =
                               Append(@, [start_ts  |-> ts,
                                          commit_ts |-> w.commit_ts,
                                          type      |-> "write"])]
            /\ key_si' = [key_si EXCEPT ![k] =
                            @ /\ (w.commit_ts > key_last_read_ts[k])]
            /\ UNCHANGED key_data
       ELSE \* Primary not committed: roll back primary and this key.
            /\ key_lock' = [kk \in KEY |->
                              IF kk = k \/ kk = p
                              THEN {x \in key_lock[kk] : x.ts # ts}
                              ELSE key_lock[kk]]
            /\ key_write' = [kk \in KEY |->
                               IF (kk = k \/ kk = p) /\ ~HasAnyRecord(kk, ts)
                               THEN Append(key_write[kk],
                                           [start_ts  |-> ts,
                                            commit_ts |-> ts,
                                            type      |-> "rollback"])
                               ELSE key_write[kk]]
            /\ key_data' = [kk \in KEY |->
                              IF kk = k \/ kk = p
                              THEN key_data[kk] \ {ts}
                              ELSE key_data[kk]]
            /\ UNCHANGED key_si
    /\ UNCHANGED <<next_ts, client_vars, key_last_read_ts>>

Get(c) ==
  /\ client_state[c] = "working"
  /\ \/ \E k \in KEY : ReadKey(c, k)
     \/ StartPrewrite(c)
     \/ \E k \in KEY : CleanupLock(c, k)

\* Prewrite: lock pending keys (primary first) and raise commit_ts above
\* last read timestamps of locked keys.
PrewriteKey(c, k) ==
  LET ts == client_ts[c].start_ts IN
  /\ key_lock[k] = {}
  /\ ~ \E w \in Range(key_write[k]) :
         \/ (w.type = "write" /\ w.commit_ts >= ts)
         \/ (w.type = "rollback" /\ w.start_ts = ts)
  /\ key_lock' = [key_lock EXCEPT ![k] =
                    {[ts |-> ts, primary |-> client_key[c].primary]}]
  /\ key_data' = [key_data EXCEPT ![k] = @ \cup {ts}]
  /\ client_ts' = [client_ts EXCEPT ![c].commit_ts =
                     Max(@, Max(ts, key_last_read_ts[k]) + 1)]
  /\ client_key' = [client_key EXCEPT ![c].pending = @ \ {k}]
  /\ UNCHANGED <<next_ts, client_state, key_write, key_last_read_ts, key_si>>

Prewrite(c) ==
  /\ client_state[c] = "prewriting"
  /\ IF client_key[c].pending = {}
     THEN /\ client_state' = [client_state EXCEPT ![c] = "committing"]
          /\ UNCHANGED <<next_ts, client_ts, client_key, key_vars>>
     ELSE IF client_key[c].primary \in client_key[c].pending
          THEN PrewriteKey(c, client_key[c].primary)
          ELSE \E k \in client_key[c].pending : PrewriteKey(c, k)

\* Commit: write the primary key's commit record if its lock still exists.
Commit(c) ==
  LET p  == client_key[c].primary
      ts == client_ts[c].start_ts
      cts == client_ts[c].commit_ts
  IN
  /\ client_state[c] = "committing"
  /\ IF \E l \in key_lock[p] : l.ts = ts
     THEN /\ key_lock' = [key_lock EXCEPT ![p] = {x \in @ : x.ts # ts}]
          /\ key_write' = [key_write EXCEPT ![p] =
                             Append(@, [start_ts  |-> ts,
                                        commit_ts |-> cts,
                                        type      |-> "write"])]
          /\ key_si' = [key_si EXCEPT ![p] = @ /\ (cts > key_last_read_ts[p])]
          /\ client_state' = [client_state EXCEPT ![c] = "committed"]
          /\ UNCHANGED <<key_data, key_last_read_ts>>
     ELSE /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
          /\ UNCHANGED key_vars
  /\ UNCHANGED <<next_ts, client_ts, client_key>>

\* Abort: halt the transaction; cleanup is left to other clients.
Abort(c) ==
  /\ client_state[c] \in {"working", "prewriting"}
  /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
  /\ UNCHANGED <<next_ts, client_ts, client_key, key_vars>>

Next ==
  \E c \in CLIENT :
    \/ Start(c)
    \/ Get(c)
    \/ Prewrite(c)
    \/ Commit(c)
    \/ Abort(c)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Safety invariants

TypeOK ==
  /\ next_ts \in Nat
  /\ client_state \in [CLIENT -> ClientStates]
  /\ client_ts \in [CLIENT -> [start_ts : Nat, commit_ts : Nat]]
  /\ client_key \in [CLIENT -> [primary : KEY,
                                secondary : SUBSET KEY,
                                pending : SUBSET KEY]]
  /\ key_data \in [KEY -> SUBSET Nat]
  /\ key_lock \in [KEY -> SUBSET LockRec]
  /\ key_write \in [KEY -> Seq(WriteRec)]
  /\ key_last_read_ts \in [KEY -> Nat]
  /\ key_si \in [KEY -> BOOLEAN]

\* Commit records on each key appear in strictly increasing commit_ts order.
WriteConsistency ==
  \A k \in KEY :
    \A i, j \in DOMAIN key_write[k] :
      (/\ i < j
       /\ key_write[k][i].type = "write"
       /\ key_write[k][j].type = "write")
      => key_write[k][i].commit_ts < key_write[k][j].commit_ts

\* At most one lock per key.
UniqueLockPerKey ==
  \A k \in KEY : Cardinality(key_lock[k]) <= 1

\* A committed client has its primary commit record, and each of its keys is
\* either still locked by it or has a write record for it.
CommittedConsistency ==
  \A c \in CLIENT :
    LET ts  == client_ts[c].start_ts
        cts == client_ts[c].commit_ts
        p   == client_key[c].primary
    IN
    client_state[c] = "committed" =>
      /\ \E w \in Range(key_write[p]) :
           /\ w.type = "write"
           /\ w.start_ts = ts
           /\ w.commit_ts = cts
      /\ \A k \in ClientKeys(c) :
           \/ \E l \in key_lock[k] : l.ts = ts
           \/ HasCommitRecord(k, ts)

\* An aborted client never has a commit record on its primary key.
AbortedConsistency ==
  \A c \in CLIENT :
    client_state[c] = "aborted" =>
      ~HasCommitRecord(client_key[c].primary, client_ts[c].start_ts)

\* No transaction is both committed and rolled back.
RollbackConsistency ==
  \A k1, k2 \in KEY :
    \A w1 \in Range(key_write[k1]), w2 \in Range(key_write[k2]) :
      (w1.type = "write" /\ w2.type = "rollback")
        => w1.start_ts # w2.start_ts

\* Per key, at most one write record per start timestamp.
UniqueWrite ==
  \A k \in KEY :
    \A i, j \in DOMAIN key_write[k] :
      i # j => key_write[k][i].start_ts # key_write[k][j].start_ts

\* Snapshot isolation: no commit at or below a recorded read timestamp.
SnapshotIsolation ==
  \A k \in KEY : key_si[k]

=============================================================================