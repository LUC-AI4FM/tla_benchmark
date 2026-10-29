------------------------- MODULE OptimizedCommitTsPercolator -------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS KEY, CLIENT, CLIENT_PRIMARY_KEY

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
key_vars == <<key_data, key_lock, key_write, key_last_read_ts, key_si>>
vars == <<next_ts, client_vars, key_vars>>

NoneTs == 0

Max(a, b) == IF a > b THEN a ELSE b

States == {"init", "working", "prewriting", "committing", "committed", "aborted"}

-----------------------------------------------------------------------------
\* Helpers

hasLockLE(k, ts) == \E l \in key_lock[k] : l.ts <= ts

hasLockEQ(k, ts) == \E l \in key_lock[k] : l.ts = ts

hasRecord(k, start) ==
  \E n \in 1..Len(key_write[k]) : key_write[k][n].start_ts = start

commitRecords(k, start) ==
  {key_write[k][n] : n \in {m \in 1..Len(key_write[k]) :
        /\ key_write[k][m].start_ts = start
        /\ key_write[k][m].type = "write"}}

rollbackRecords(k, start) ==
  {key_write[k][n] : n \in {m \in 1..Len(key_write[k]) :
        /\ key_write[k][m].start_ts = start
        /\ key_write[k][m].type = "rollback"}}

hasNewerOrEqualWrite(k, ts) ==
  \E n \in 1..Len(key_write[k]) : key_write[k][n].ts >= ts

\* Roll back the transaction with start_ts ts on all keys in ks.
rollbackKeys(ks, ts) ==
  /\ key_lock' = [kk \in KEY |->
        IF kk \in ks THEN {l \in key_lock[kk] : l.ts # ts} ELSE key_lock[kk]]
  /\ key_write' = [kk \in KEY |->
        IF kk \in ks /\ ~hasRecord(kk, ts)
          THEN Append(key_write[kk], [ts |-> ts, start_ts |-> ts, type |-> "rollback"])
          ELSE key_write[kk]]
  /\ UNCHANGED <<key_data, key_last_read_ts, key_si>>

\* Clean up a stale lock on key k whose ts is <= ts.
cleanupStaleLock(k, ts) ==
  \E l \in key_lock[k] :
    /\ l.ts <= ts
    /\ LET p == l.primary
           cr == commitRecords(p, l.ts)
       IN IF cr # {}
            THEN \E w \in cr :
                   /\ key_lock' = [key_lock EXCEPT ![k] = @ \ {l}]
                   /\ key_write' = [key_write EXCEPT ![k] =
                         Append(@, [ts |-> w.ts, start_ts |-> l.ts, type |-> "write"])]
                   /\ key_si' = [key_si EXCEPT ![k] =
                         @ /\ (w.ts > key_last_read_ts[k])]
                   /\ UNCHANGED <<key_data, key_last_read_ts>>
            ELSE rollbackKeys({k, p}, l.ts)

-----------------------------------------------------------------------------
Init ==
  /\ next_ts = 1
  /\ client_state = [c \in CLIENT |-> "init"]
  /\ client_ts = [c \in CLIENT |-> [start_ts |-> NoneTs, commit_ts |-> NoneTs]]
  /\ client_key = [c \in CLIENT |->
        [primary |-> CLIENT_PRIMARY_KEY[c],
         secondary |-> KEY \ {CLIENT_PRIMARY_KEY[c]},
         pending |-> KEY]]
  /\ key_data = [k \in KEY |-> {}]
  /\ key_lock = [k \in KEY |-> {}]
  /\ key_write = [k \in KEY |-> <<>>]
  /\ key_last_read_ts = [k \in KEY |-> 0]
  /\ key_si = [k \in KEY |-> TRUE]

Start(c) ==
  /\ client_state[c] = "init"
  /\ next_ts' = next_ts + 1
  /\ client_state' = [client_state EXCEPT ![c] = "working"]
  /\ client_ts' = [client_ts EXCEPT ![c].start_ts = next_ts]
  /\ UNCHANGED <<client_key, key_vars>>

Get(c) ==
  /\ client_state[c] = "working"
  /\ LET start == client_ts[c].start_ts IN
     \/ \* Read some key successfully (no blocking lock).
        /\ \E k \in KEY :
             /\ ~hasLockLE(k, start)
             /\ key_last_read_ts' = [key_last_read_ts EXCEPT ![k] = Max(@, start)]
        /\ UNCHANGED <<next_ts, client_vars, key_data, key_lock, key_write, key_si>>
     \/ \* Clean up a stale lock blocking a read.
        /\ \E k \in KEY : cleanupStaleLock(k, start)
        /\ UNCHANGED <<next_ts, client_vars>>
     \/ \* Advance to prewrite phase.
        /\ client_state' = [client_state EXCEPT ![c] = "prewriting"]
        /\ client_ts' = [client_ts EXCEPT ![c].commit_ts = start + 1]
        /\ UNCHANGED <<next_ts, client_key, key_vars>>

Prewrite(c) ==
  /\ client_state[c] = "prewriting"
  /\ client_key[c].pending # {}
  /\ LET start == client_ts[c].start_ts IN
     \E k \in client_key[c].pending :
       /\ key_lock[k] = {}
       /\ ~hasNewerOrEqualWrite(k, start)
       /\ key_lock' = [key_lock EXCEPT ![k] = {[ts |-> start, primary |-> client_key[c].primary]}]
       /\ key_data' = [key_data EXCEPT ![k] = @ \cup {start}]
       /\ client_key' = [client_key EXCEPT ![c].pending = @ \ {k}]
       /\ client_ts' = [client_ts EXCEPT ![c].commit_ts =
                          Max(@, key_last_read_ts[k] + 1)]
       /\ client_state' = [client_state EXCEPT ![c] =
                          IF client_key[c].pending = {k} THEN "committing" ELSE "prewriting"]
       /\ UNCHANGED <<next_ts, key_write, key_last_read_ts, key_si>>

Commit(c) ==
  /\ client_state[c] = "committing"
  /\ LET start == client_ts[c].start_ts
         cts == client_ts[c].commit_ts
         p == client_key[c].primary
     IN /\ hasLockEQ(p, start)
        /\ key_lock' = [key_lock EXCEPT ![p] = {l \in @ : l.ts # start}]
        /\ key_write' = [key_write EXCEPT ![p] =
              Append(@, [ts |-> cts, start_ts |-> start, type |-> "write"])]
        /\ key_si' = [key_si EXCEPT ![p] = @ /\ (cts > key_last_read_ts[p])]
        /\ client_state' = [client_state EXCEPT ![c] = "committed"]
        /\ UNCHANGED <<next_ts, client_ts, client_key, key_data, key_last_read_ts>>

Abort(c) ==
  /\ client_state[c] \in {"working", "prewriting", "committing"}
  /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
  /\ UNCHANGED <<next_ts, client_ts, client_key, key_vars>>

Next ==
  \E c \in CLIENT :
    \/ Start(c)
    \/ Get(c)
    \/ Prewrite(c)
    \/ Commit(c)
    \/ Abort(c)

PercolatorSpec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Invariants

TypeInvariant ==
  /\ next_ts \in Nat
  /\ client_state \in [CLIENT -> States]
  /\ \A c \in CLIENT :
       /\ client_ts[c].start_ts \in Nat
       /\ client_ts[c].commit_ts \in Nat
       /\ client_key[c].primary \in KEY
       /\ client_key[c].secondary \subseteq KEY
       /\ client_key[c].pending \subseteq KEY
  /\ \A k \in KEY :
       /\ \A d \in key_data[k] : d \in Nat
       /\ \A l \in key_lock[k] : l.ts \in Nat /\ l.primary \in KEY
       /\ \A n \in 1..Len(key_write[k]) :
            /\ key_write[k][n].ts \in Nat
            /\ key_write[k][n].start_ts \in Nat
            /\ key_write[k][n].type \in {"write", "rollback"}
       /\ key_last_read_ts[k] \in Nat
       /\ key_si[k] \in BOOLEAN

WriteConsistency ==
  \A k \in KEY :
    \A n \in 1..Len(key_write[k]) :
      LET rec == key_write[k][n] IN
        IF rec.type = "write"
          THEN /\ rec.start_ts < rec.ts
               /\ rec.start_ts \in key_data[k]
          ELSE rec.start_ts = rec.ts

LockConsistency ==
  \A k \in KEY :
    /\ Cardinality(key_lock[k]) <= 1
    /\ \A l \in key_lock[k] : ~hasRecord(k, l.ts)

CommittedConsistency ==
  \A c \in CLIENT :
    LET start == client_ts[c].start_ts
        cts == client_ts[c].commit_ts
        p == client_key[c].primary
    IN client_state[c] = "committed" =>
         /\ start < cts
         /\ [ts |-> cts, start_ts |-> start, type |-> "write"] \in commitRecords(p, start)
         /\ \A k \in client_key[c].secondary :
              \/ hasLockEQ(k, start)
              \/ [ts |-> cts, start_ts |-> start, type |-> "write"] \in commitRecords(k, start)

AbortedConsistency ==
  \A c \in CLIENT :
    client_state[c] = "aborted" =>
      \A k \in KEY : commitRecords(k, client_ts[c].start_ts) = {}

RollbackConsistency ==
  \A c \in CLIENT :
    LET start == client_ts[c].start_ts IN
      start # NoneTs =>
        ~( /\ \E k \in KEY : commitRecords(k, start) # {}
           /\ \E k \in KEY : rollbackRecords(k, start) # {} )

UniqueWrite ==
  \A k \in KEY :
    \A i, j \in 1..Len(key_write[k]) :
      key_write[k][i].start_ts = key_write[k][j].start_ts => i = j

SnapshotIsolation == \A k \in KEY : key_si[k]

=============================================================================