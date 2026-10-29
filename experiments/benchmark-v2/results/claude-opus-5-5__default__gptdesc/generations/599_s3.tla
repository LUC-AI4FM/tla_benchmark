---------------------------- MODULE OptimizedPercolator ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS CLIENT,          \* set of clients (transactions)
          KEY,             \* set of keys
          CLIENT_PRIMARY,  \* CLIENT_PRIMARY[c] : the primary key of client c
          CLIENT_KEY       \* CLIENT_KEY[c]     : the set of keys written by client c

ASSUME /\ CLIENT_KEY \in [CLIENT -> SUBSET KEY]
       /\ CLIENT_PRIMARY \in [CLIENT -> KEY]
       /\ \A c \in CLIENT : CLIENT_PRIMARY[c] \in CLIENT_KEY[c]

VARIABLES next_ts,       \* global timestamp oracle
          client_state,  \* state of each client
          client_ts,     \* start / commit timestamps of each client
          client_key,    \* keys that still need to be prewritten by each client
          key_lock,      \* per-key lock (set with at most one element)
          key_write,     \* per-key sequence of write / rollback records
          key_data,      \* per-key set of start timestamps of written data
          key_si         \* per-key snapshot-isolation indicator

vars == <<next_ts, client_state, client_ts, client_key,
          key_lock, key_write, key_data, key_si>>

-----------------------------------------------------------------------------------
ClientStates == {"init", "working", "prewriting", "committing", "committed", "aborted"}

LockRec  == [ts : Nat, primary : KEY]
WriteRec == [start_ts : Nat, commit_ts : Nat, type : {"write", "rollback"}]
TsRec    == [start_ts : Nat, commit_ts : Nat]

Range(s) == {s[i] : i \in DOMAIN s}

\* A key can be locked by a transaction with start timestamp ts if it is not
\* locked and no write/rollback record exists with commit_ts >= ts.
CanLockKey(k, ts) ==
  /\ key_lock[k] = {}
  /\ \A w \in Range(key_write[k]) : w.commit_ts < ts

\* Append a record to the write column of key k, updating the SI indicator:
\* snapshot isolation is violated if a committed write to k has a commit
\* timestamp not smaller than the start timestamp of the newly committed write.
AppendWrite(k, w) ==
  /\ key_write' = [key_write EXCEPT ![k] = Append(@, w)]
  /\ key_si' = [key_si EXCEPT ![k] =
                  @ /\ (w.type = "write" =>
                          \A x \in Range(key_write[k]) :
                             x.type = "write" => x.commit_ts < w.start_ts)]

-----------------------------------------------------------------------------------
Init ==
  /\ next_ts = 0
  /\ client_state = [c \in CLIENT |-> "init"]
  /\ client_ts = [c \in CLIENT |-> [start_ts |-> 0, commit_ts |-> 0]]
  /\ client_key = [c \in CLIENT |-> {}]
  /\ key_lock = [k \in KEY |-> {}]
  /\ key_write = [k \in KEY |-> <<>>]
  /\ key_data = [k \in KEY |-> {}]
  /\ key_si = [k \in KEY |-> TRUE]

\* Client obtains a start timestamp and begins working.
Start(c) ==
  /\ client_state[c] = "init"
  /\ next_ts' = next_ts + 1
  /\ client_state' = [client_state EXCEPT ![c] = "working"]
  /\ client_ts' = [client_ts EXCEPT ![c].start_ts = next_ts']
  /\ UNCHANGED <<client_key, key_lock, key_write, key_data, key_si>>

\* Client reads a key: only possible when no lock with an older timestamp
\* blocks the read. Reading does not modify the state.
Get(c) ==
  /\ client_state[c] = "working"
  /\ \E k \in CLIENT_KEY[c] :
       \A l \in key_lock[k] : l.ts > client_ts[c].start_ts
  /\ UNCHANGED vars

\* Client cleans up a stale lock (one with an older start timestamp) on a key
\* it wants to read, by rolling the owner transaction forward or backward.
CleanupStaleLock(c) ==
  /\ client_state[c] = "working"
  /\ \E k \in CLIENT_KEY[c] :
       \E l \in key_lock[k] :
         /\ l.ts < client_ts[c].start_ts
         /\ LET p == l.primary
                committed == {w \in Range(key_write[p]) :
                                 w.start_ts = l.ts /\ w.type = "write"}
                rb == [start_ts |-> l.ts, commit_ts |-> l.ts, type |-> "rollback"]
            IN IF committed # {}
               THEN \* primary committed: roll the secondary forward
                    \E w \in committed :
                      /\ key_lock' = [key_lock EXCEPT ![k] = @ \ {l}]
                      /\ AppendWrite(k, [start_ts |-> l.ts,
                                         commit_ts |-> w.commit_ts,
                                         type |-> "write"])
                      /\ UNCHANGED key_data
               ELSE IF \E pl \in key_lock[p] : pl.ts = l.ts
               THEN \* primary still locked: roll back the primary
                    /\ key_lock' = [key_lock EXCEPT ![p] = {}]
                    /\ key_data' = [key_data EXCEPT ![p] = @ \ {l.ts}]
                    /\ AppendWrite(p, rb)
               ELSE \* primary rolled back: roll back this lock
                    /\ key_lock' = [key_lock EXCEPT ![k] = @ \ {l}]
                    /\ key_data' = [key_data EXCEPT ![k] = @ \ {l.ts}]
                    /\ AppendWrite(k, rb)
  /\ UNCHANGED <<next_ts, client_state, client_ts, client_key>>

\* Client prewrites (locks) its primary key first.
PrewritePrimary(c) ==
  /\ client_state[c] = "working"
  /\ LET p  == CLIENT_PRIMARY[c]
         ts == client_ts[c].start_ts
     IN IF CanLockKey(p, ts)
        THEN /\ key_lock' = [key_lock EXCEPT ![p] = {[ts |-> ts, primary |-> p]}]
             /\ key_data' = [key_data EXCEPT ![p] = @ \cup {ts}]
             /\ client_key' = [client_key EXCEPT ![c] = CLIENT_KEY[c] \ {p}]
             /\ client_state' = [client_state EXCEPT ![c] = "prewriting"]
        ELSE /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
             /\ UNCHANGED <<key_lock, key_data, client_key>>
  /\ UNCHANGED <<next_ts, client_ts, key_write, key_si>>

\* Client prewrites (locks) one of its secondary keys.
PrewriteSecondary(c) ==
  /\ client_state[c] = "prewriting"
  /\ \E k \in client_key[c] :
       LET p  == CLIENT_PRIMARY[c]
           ts == client_ts[c].start_ts
       IN IF CanLockKey(k, ts)
          THEN /\ key_lock' = [key_lock EXCEPT ![k] = {[ts |-> ts, primary |-> p]}]
               /\ key_data' = [key_data EXCEPT ![k] = @ \cup {ts}]
               /\ client_key' = [client_key EXCEPT ![c] = @ \ {k}]
               /\ UNCHANGED client_state
          ELSE /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
               /\ UNCHANGED <<key_lock, key_data, client_key>>
  /\ UNCHANGED <<next_ts, client_ts, key_write, key_si>>

\* After all keys are prewritten, the client obtains a commit timestamp.
StartCommit(c) ==
  /\ client_state[c] = "prewriting"
  /\ client_key[c] = {}
  /\ next_ts' = next_ts + 1
  /\ client_ts' = [client_ts EXCEPT ![c].commit_ts = next_ts']
  /\ client_state' = [client_state EXCEPT ![c] = "committing"]
  /\ UNCHANGED <<client_key, key_lock, key_write, key_data, key_si>>

\* Client commits only the primary key; secondaries are resolved lazily.
CommitPrimary(c) ==
  /\ client_state[c] = "committing"
  /\ LET p  == CLIENT_PRIMARY[c]
         ts == client_ts[c].start_ts
     IN IF \E l \in key_lock[p] : l.ts = ts
        THEN /\ key_lock' = [key_lock EXCEPT ![p] = {}]
             /\ AppendWrite(p, [start_ts |-> ts,
                                commit_ts |-> client_ts[c].commit_ts,
                                type |-> "write"])
             /\ client_state' = [client_state EXCEPT ![c] = "committed"]
        ELSE /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
             /\ UNCHANGED <<key_lock, key_write, key_si>>
  /\ UNCHANGED <<next_ts, client_ts, client_key, key_data>>

\* Client voluntarily aborts; any locks left behind are cleaned up by others.
ClientAbort(c) ==
  /\ client_state[c] \in {"working", "prewriting"}
  /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
  /\ UNCHANGED <<next_ts, client_ts, client_key, key_lock, key_write, key_data, key_si>>

Next ==
  \E c \in CLIENT :
    \/ Start(c)
    \/ Get(c)
    \/ CleanupStaleLock(c)
    \/ PrewritePrimary(c)
    \/ PrewriteSecondary(c)
    \/ StartCommit(c)
    \/ CommitPrimary(c)
    \/ ClientAbort(c)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------------
\* Invariants

TypeOK ==
  /\ next_ts \in Nat
  /\ client_state \in [CLIENT -> ClientStates]
  /\ client_ts \in [CLIENT -> TsRec]
  /\ client_key \in [CLIENT -> SUBSET KEY]
  /\ key_lock \in [KEY -> SUBSET LockRec]
  /\ key_write \in [KEY -> Seq(WriteRec)]
  /\ key_data \in [KEY -> SUBSET Nat]
  /\ key_si \in [KEY -> BOOLEAN]

\* Write records on each key are strictly ordered by commit timestamp,
\* and each record's commit timestamp is not smaller than its start timestamp.
WriteConsistency ==
  \A k \in KEY :
    /\ \A i \in DOMAIN key_write[k] :
         key_write[k][i].start_ts <= key_write[k][i].commit_ts
    /\ \A i, j \in DOMAIN key_write[k] :
         i < j => key_write[k][i].commit_ts < key_write[k][j].commit_ts

\* Each key has at most one lock, the locked data is present, and a locked
\* transaction has neither committed nor rolled back on that key.
LockConsistency ==
  \A k \in KEY :
    /\ Cardinality(key_lock[k]) <= 1
    /\ \A l \in key_lock[k] :
         /\ l.ts \in key_data[k]
         /\ \A w \in Range(key_write[k]) : w.start_ts # l.ts

\* A committed client has a commit record on its primary key, and every
\* secondary key is either committed with the same timestamps or still locked.
CommittedConsistency ==
  \A c \in CLIENT :
    client_state[c] = "committed" =>
      LET st == client_ts[c].start_ts
          ct == client_ts[c].commit_ts
          committedOn(k) == [start_ts |-> st, commit_ts |-> ct, type |-> "write"]
                               \in Range(key_write[k])
      IN /\ committedOn(CLIENT_PRIMARY[c])
         /\ \A k \in CLIENT_KEY[c] :
              \/ committedOn(k)
              \/ (k # CLIENT_PRIMARY[c] /\ \E l \in key_lock[k] : l.ts = st)
         /\ \A k \in KEY :
              \A w \in Range(key_write[k]) :
                 ~(w.start_ts = st /\ w.type = "rollback")

\* An aborted client never has any of its writes committed.
AbortedConsistency ==
  \A c \in CLIENT :
    client_state[c] = "aborted" =>
      \A k \in KEY :
        \A w \in Range(key_write[k]) :
          ~(w.start_ts = client_ts[c].start_ts /\ w.type = "write")

\* A transaction can never be both rolled back and committed.
RollbackConsistency ==
  \A k1, k2 \in KEY :
    \A w1 \in Range(key_write[k1]) :
      \A w2 \in Range(key_write[k2]) :
        (w1.type = "rollback" /\ w2.type = "write") => w1.start_ts # w2.start_ts

\* The snapshot-isolation indicator is preserved on every key.
SnapshotIsolation ==
  \A k \in KEY : key_si[k] = TRUE

THEOREM Spec => [](/\ TypeOK
                   /\ WriteConsistency
                   /\ LockConsistency
                   /\ CommittedConsistency
                   /\ AbortedConsistency
                   /\ RollbackConsistency
                   /\ SnapshotIsolation)
===================================================================================