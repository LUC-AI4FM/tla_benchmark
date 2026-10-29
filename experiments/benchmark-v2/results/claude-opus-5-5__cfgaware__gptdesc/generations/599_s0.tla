---------------------------- MODULE Percolator ----------------------------
EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS KEY, CLIENT, CLIENT_PRIMARY_KEY

VARIABLES next_ts, client_state, client_ts, client_key,
          key_lock, key_write, key_data, key_si

client_vars == <<client_state, client_ts, client_key>>
key_vars == <<key_lock, key_write, key_data, key_si>>
vars == <<next_ts, client_vars, key_vars>>

NoneTs == 0

ClientStates == {"init", "working", "prewriting", "committing", "committed", "aborted"}

WriteRec == [start_ts : Nat, commit_ts : Nat, type : {"write", "rollback"}]

HasWrite(k, ts) ==
  \E i \in 1..Len(key_write[k]) :
    /\ key_write[k][i].start_ts = ts
    /\ key_write[k][i].type = "write"

HasRollback(k, ts) ==
  \E i \in 1..Len(key_write[k]) :
    /\ key_write[k][i].start_ts = ts
    /\ key_write[k][i].type = "rollback"

HasLock(k, ts) == \E l \in key_lock[k] : l.ts = ts

CommitTsOf(k, ts) ==
  LET i == CHOOSE i \in 1..Len(key_write[k]) :
             /\ key_write[k][i].start_ts = ts
             /\ key_write[k][i].type = "write"
  IN key_write[k][i].commit_ts

\* Snapshot isolation check: no other write committed at or after our start_ts.
SIOk(k, start) ==
  \A i \in 1..Len(key_write[k]) :
    key_write[k][i].type = "write" => key_write[k][i].commit_ts < start

-----------------------------------------------------------------------------

Init ==
  /\ next_ts = 1
  /\ client_state = [c \in CLIENT |-> "init"]
  /\ client_ts = [c \in CLIENT |-> [start_ts |-> NoneTs, commit_ts |-> NoneTs]]
  /\ client_key = [c \in CLIENT |->
                     [primary |-> CLIENT_PRIMARY_KEY[c],
                      secondary |-> KEY \ {CLIENT_PRIMARY_KEY[c]},
                      pending |-> KEY]]
  /\ key_lock = [k \in KEY |-> {}]
  /\ key_write = [k \in KEY |-> <<>>]
  /\ key_data = [k \in KEY |-> {}]
  /\ key_si = [k \in KEY |-> TRUE]

Start(c) ==
  /\ client_state[c] = "init"
  /\ next_ts' = next_ts + 1
  /\ client_state' = [client_state EXCEPT ![c] = "working"]
  /\ client_ts' = [client_ts EXCEPT ![c].start_ts = next_ts]
  /\ UNCHANGED <<client_key, key_vars>>

\* Read a key: only possible when there is no lock older than start_ts.
Get(c) ==
  /\ client_state[c] = "working"
  /\ \E k \in KEY :
       ~\E l \in key_lock[k] : l.ts < client_ts[c].start_ts
  /\ UNCHANGED vars

\* Clean up a stale lock encountered while reading.
CleanupStaleLock(c) ==
  /\ client_state[c] = "working"
  /\ \E k \in KEY :
     \E l \in key_lock[k] :
       LET p == l.primary
           ts == l.ts
       IN
       /\ ts < client_ts[c].start_ts
       /\ \/ \* Primary still locked: roll back the primary.
             /\ HasLock(p, ts)
             /\ key_lock' = [key_lock EXCEPT ![p] = {}]
             /\ key_data' = [key_data EXCEPT ![p] = @ \ {ts}]
             /\ key_write' = [key_write EXCEPT ![p] =
                    Append(@, [start_ts |-> ts, commit_ts |-> ts, type |-> "rollback"])]
             /\ UNCHANGED key_si
          \/ \* Primary committed: commit the secondary.
             /\ ~HasLock(p, ts)
             /\ HasWrite(p, ts)
             /\ key_lock' = [key_lock EXCEPT ![k] = {}]
             /\ key_write' = [key_write EXCEPT ![k] =
                    Append(@, [start_ts |-> ts, commit_ts |-> CommitTsOf(p, ts),
                               type |-> "write"])]
             /\ key_si' = [key_si EXCEPT ![k] = @ /\ SIOk(k, ts)]
             /\ UNCHANGED key_data
          \/ \* Primary rolled back: roll back the secondary.
             /\ ~HasLock(p, ts)
             /\ ~HasWrite(p, ts)
             /\ HasRollback(p, ts)
             /\ key_lock' = [key_lock EXCEPT ![k] = {}]
             /\ key_data' = [key_data EXCEPT ![k] = @ \ {ts}]
             /\ key_write' = [key_write EXCEPT ![k] =
                    Append(@, [start_ts |-> ts, commit_ts |-> ts, type |-> "rollback"])]
             /\ UNCHANGED key_si
  /\ UNCHANGED <<next_ts, client_vars>>

StartPrewrite(c) ==
  /\ client_state[c] = "working"
  /\ client_state' = [client_state EXCEPT ![c] = "prewriting"]
  /\ UNCHANGED <<next_ts, client_ts, client_key, key_vars>>

Prewrite(c) ==
  /\ client_state[c] = "prewriting"
  /\ \E k \in client_key[c].pending :
       LET start == client_ts[c].start_ts
           p == client_key[c].primary
       IN
       /\ (k # p) => (p \notin client_key[c].pending)
       /\ key_lock[k] = {}
       /\ \A i \in 1..Len(key_write[k]) : key_write[k][i].commit_ts < start
       /\ key_lock' = [key_lock EXCEPT ![k] = {[ts |-> start, primary |-> p]}]
       /\ key_data' = [key_data EXCEPT ![k] = @ \cup {start}]
       /\ client_key' = [client_key EXCEPT ![c].pending = @ \ {k}]
  /\ UNCHANGED <<next_ts, client_state, client_ts, key_write, key_si>>

GetCommitTs(c) ==
  /\ client_state[c] = "prewriting"
  /\ client_key[c].pending = {}
  /\ next_ts' = next_ts + 1
  /\ client_ts' = [client_ts EXCEPT ![c].commit_ts = next_ts]
  /\ client_state' = [client_state EXCEPT ![c] = "committing"]
  /\ UNCHANGED <<client_key, key_vars>>

CommitPrimary(c) ==
  /\ client_state[c] = "committing"
  /\ LET p == client_key[c].primary
         start == client_ts[c].start_ts
         commit == client_ts[c].commit_ts
     IN
     IF HasLock(p, start)
     THEN /\ key_lock' = [key_lock EXCEPT ![p] = {}]
          /\ key_write' = [key_write EXCEPT ![p] =
                 Append(@, [start_ts |-> start, commit_ts |-> commit, type |-> "write"])]
          /\ key_si' = [key_si EXCEPT ![p] = @ /\ SIOk(p, start)]
          /\ client_state' = [client_state EXCEPT ![c] = "committed"]
          /\ UNCHANGED key_data
     ELSE /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
          /\ UNCHANGED <<key_lock, key_write, key_si, key_data>>
  /\ UNCHANGED <<next_ts, client_ts, client_key>>

Abort(c) ==
  /\ client_state[c] \in {"working", "prewriting"}
  /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
  /\ UNCHANGED <<next_ts, client_ts, client_key, key_vars>>

Next ==
  \E c \in CLIENT :
    \/ Start(c)
    \/ Get(c)
    \/ CleanupStaleLock(c)
    \/ StartPrewrite(c)
    \/ Prewrite(c)
    \/ GetCommitTs(c)
    \/ CommitPrimary(c)
    \/ Abort(c)

PercolatorSpec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

TypeInvariant ==
  /\ next_ts \in Nat
  /\ client_state \in [CLIENT -> ClientStates]
  /\ client_ts \in [CLIENT -> [start_ts : Nat, commit_ts : Nat]]
  /\ client_key \in [CLIENT -> [primary : KEY, secondary : SUBSET KEY,
                                pending : SUBSET KEY]]
  /\ key_lock \in [KEY -> SUBSET [ts : Nat, primary : KEY]]
  /\ key_write \in [KEY -> Seq(WriteRec)]
  /\ key_data \in [KEY -> SUBSET Nat]
  /\ key_si \in [KEY -> BOOLEAN]

\* Committed writes are ordered by commit_ts, and start_ts < commit_ts.
WriteConsistency ==
  \A k \in KEY :
    /\ \A i \in 1..Len(key_write[k]) :
         key_write[k][i].type = "write" =>
           key_write[k][i].start_ts < key_write[k][i].commit_ts
    /\ \A i, j \in 1..Len(key_write[k]) :
         (/\ i < j
          /\ key_write[k][i].type = "write"
          /\ key_write[k][j].type = "write")
         => key_write[k][i].commit_ts < key_write[k][j].commit_ts

\* Each transaction has at most one record per key.
UniqueWrite ==
  \A k \in KEY :
    \A i, j \in 1..Len(key_write[k]) :
      (i # j) => key_write[k][i].start_ts # key_write[k][j].start_ts

\* At most one lock per key, and a lock never coexists with a record of its txn.
LockConsistency ==
  \A k \in KEY :
    /\ Cardinality(key_lock[k]) <= 1
    /\ \A l \in key_lock[k] :
         ~\E i \in 1..Len(key_write[k]) : key_write[k][i].start_ts = l.ts

CommittedConsistency ==
  \A c \in CLIENT :
    LET start == client_ts[c].start_ts
        commit == client_ts[c].commit_ts
        p == client_key[c].primary
    IN
    client_state[c] = "committed" =>
      /\ HasWrite(p, start)
      /\ CommitTsOf(p, start) = commit
      /\ \A k \in client_key[c].secondary :
           /\ HasLock(k, start) \/ (HasWrite(k, start) /\ CommitTsOf(k, start) = commit)
           /\ ~HasRollback(k, start)

AbortedConsistency ==
  \A c \in CLIENT :
    client_state[c] = "aborted" =>
      \A k \in KEY : ~HasWrite(k, client_ts[c].start_ts)

RollbackConsistency ==
  \A c \in CLIENT :
    LET start == client_ts[c].start_ts IN
    (start # NoneTs /\ \E k \in KEY : HasRollback(k, start))
      => ~HasWrite(client_key[c].primary, start)

SnapshotIsolation == \A k \in KEY : key_si[k]

=============================================================================