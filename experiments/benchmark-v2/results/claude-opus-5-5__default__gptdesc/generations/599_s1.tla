---------------------------- MODULE Percolator ----------------------------
EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS CLIENT, KEY, CLIENT_PRIMARY, CLIENT_KEY

ASSUME CLIENT_KEY \in [CLIENT -> SUBSET KEY]
ASSUME CLIENT_PRIMARY \in [CLIENT -> KEY]
ASSUME \A c \in CLIENT : CLIENT_PRIMARY[c] \in CLIENT_KEY[c]

VARIABLES next_ts, client_state, client_ts, client_key,
          key_lock, key_write, key_data, key_si

client_vars == <<client_state, client_ts, client_key>>
key_vars    == <<key_lock, key_write, key_data, key_si>>
vars        == <<next_ts, client_vars, key_vars>>

Ts == Nat
NoneTs == 0

States == {"init", "working", "prewriting", "committing", "committed", "aborted"}

-----------------------------------------------------------------------------
\* Helpers

WritesOf(k) == {key_write[k][i] : i \in DOMAIN key_write[k]}

hasLockLE(k, ts) == \E l \in key_lock[k] : l.ts <= ts
hasLockEQ(k, ts) == \E l \in key_lock[k] : l.ts = ts

hasCommit(k, ts)   == \E w \in WritesOf(k) : w.type = "write" /\ w.start_ts = ts
hasRollback(k, ts) == \E w \in WritesOf(k) : w.type = "rollback" /\ w.start_ts = ts

CommitTsOf(k, ts) ==
    (CHOOSE w \in WritesOf(k) : w.type = "write" /\ w.start_ts = ts).ts

canLock(k, ts) ==
    /\ key_lock[k] = {}
    /\ ~\E w \in WritesOf(k) : w.ts >= ts

\* Roll back the locks with start ts = ts on the keys in K.
RollbackKeys(K, ts) ==
    /\ key_lock' = [k \in KEY |->
          IF k \in K THEN {l \in key_lock[k] : l.ts # ts} ELSE key_lock[k]]
    /\ key_data' = [k \in KEY |->
          IF k \in K THEN key_data[k] \ {[ts |-> ts]} ELSE key_data[k]]
    /\ key_write' = [k \in KEY |->
          IF k \in K
          THEN Append(key_write[k], [ts |-> ts, start_ts |-> ts, type |-> "rollback"])
          ELSE key_write[k]]
    /\ UNCHANGED key_si

\* Commit key k for the transaction with start ts "start" at commit ts "commit".
\* The snapshot-isolation indicator is falsified if another write was committed
\* on k after this transaction's start ts (a lost write-write conflict).
CommitKey(k, start, commit) ==
    /\ key_lock'  = [key_lock EXCEPT ![k] = {l \in @ : l.ts # start}]
    /\ key_write' = [key_write EXCEPT ![k] =
                        Append(@, [ts |-> commit, start_ts |-> start, type |-> "write"])]
    /\ key_si'    = [key_si EXCEPT ![k] =
                        @ /\ ~\E w \in WritesOf(k) : w.type = "write" /\ w.ts > start]
    /\ UNCHANGED key_data

-----------------------------------------------------------------------------
TypeOK ==
    /\ next_ts \in Ts
    /\ client_state \in [CLIENT -> States]
    /\ client_ts \in [CLIENT -> [start_ts : Ts, commit_ts : Ts]]
    /\ client_key \in [CLIENT -> [primary : KEY, secondary : SUBSET KEY, pending : SUBSET KEY]]
    /\ key_lock \in [KEY -> SUBSET [ts : Ts, primary : KEY]]
    /\ key_write \in [KEY -> Seq([ts : Ts, start_ts : Ts, type : {"write", "rollback"}])]
    /\ key_data \in [KEY -> SUBSET [ts : Ts]]
    /\ key_si \in [KEY -> BOOLEAN]

Init ==
    /\ next_ts = 1
    /\ client_state = [c \in CLIENT |-> "init"]
    /\ client_ts = [c \in CLIENT |-> [start_ts |-> NoneTs, commit_ts |-> NoneTs]]
    /\ client_key = [c \in CLIENT |->
                        [primary   |-> CLIENT_PRIMARY[c],
                         secondary |-> CLIENT_KEY[c] \ {CLIENT_PRIMARY[c]},
                         pending   |-> {}]]
    /\ key_lock = [k \in KEY |-> {}]
    /\ key_write = [k \in KEY |-> <<>>]
    /\ key_data = [k \in KEY |-> {}]
    /\ key_si = [k \in KEY |-> TRUE]

-----------------------------------------------------------------------------
\* Client actions

Start(c) ==
    /\ client_state[c] = "init"
    /\ client_state' = [client_state EXCEPT ![c] = "working"]
    /\ client_ts' = [client_ts EXCEPT ![c].start_ts = next_ts]
    /\ next_ts' = next_ts + 1
    /\ UNCHANGED <<client_key, key_vars>>

\* Snapshot read: only possible when no lock older than start ts blocks it.
Get(c, k) ==
    /\ client_state[c] = "working"
    /\ ~hasLockLE(k, client_ts[c].start_ts)
    /\ UNCHANGED vars

\* Clean up a stale lock encountered by a reader.
Cleanup(c, k) ==
    /\ client_state[c] = "working"
    /\ \E l \in key_lock[k] :
         /\ l.ts < client_ts[c].start_ts
         /\ LET p == l.primary
                s == l.ts
            IN IF hasLockEQ(p, s)
               THEN RollbackKeys({p, k}, s)
               ELSE IF hasCommit(p, s)
                    THEN CommitKey(k, s, CommitTsOf(p, s))
                    ELSE RollbackKeys({k}, s)
    /\ UNCHANGED <<next_ts, client_vars>>

StartPrewrite(c) ==
    /\ client_state[c] = "working"
    /\ client_state' = [client_state EXCEPT ![c] = "prewriting"]
    /\ client_key' = [client_key EXCEPT ![c].pending = CLIENT_KEY[c]]
    /\ UNCHANGED <<next_ts, client_ts, key_vars>>

\* Optimized: the primary key is always locked before any secondary.
Prewrite(c, k) ==
    /\ client_state[c] = "prewriting"
    /\ k \in client_key[c].pending
    /\ (k = client_key[c].primary \/ client_key[c].primary \notin client_key[c].pending)
    /\ LET s == client_ts[c].start_ts IN
         IF canLock(k, s)
         THEN /\ key_lock' = [key_lock EXCEPT ![k] =
                                @ \cup {[ts |-> s, primary |-> client_key[c].primary]}]
              /\ key_data' = [key_data EXCEPT ![k] = @ \cup {[ts |-> s]}]
              /\ client_key' = [client_key EXCEPT ![c].pending = @ \ {k}]
              /\ UNCHANGED <<client_state, key_write, key_si>>
         ELSE /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
              /\ UNCHANGED <<client_key, key_vars>>
    /\ UNCHANGED <<next_ts, client_ts>>

StartCommit(c) ==
    /\ client_state[c] = "prewriting"
    /\ client_key[c].pending = {}
    /\ client_state' = [client_state EXCEPT ![c] = "committing"]
    /\ client_ts' = [client_ts EXCEPT ![c].commit_ts = next_ts]
    /\ next_ts' = next_ts + 1
    /\ UNCHANGED <<client_key, key_vars>>

CommitPrimary(c) ==
    /\ client_state[c] = "committing"
    /\ LET p == client_key[c].primary
           s == client_ts[c].start_ts
       IN IF hasLockEQ(p, s)
          THEN /\ CommitKey(p, s, client_ts[c].commit_ts)
               /\ client_state' = [client_state EXCEPT ![c] = "committed"]
          ELSE /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
               /\ UNCHANGED key_vars
    /\ UNCHANGED <<next_ts, client_ts, client_key>>

\* Asynchronous commit of secondaries after the primary is committed.
CommitSecondary(c, k) ==
    /\ client_state[c] = "committed"
    /\ k \in client_key[c].secondary
    /\ client_key' = [client_key EXCEPT ![c].secondary = @ \ {k}]
    /\ IF hasLockEQ(k, client_ts[c].start_ts)
       THEN CommitKey(k, client_ts[c].start_ts, client_ts[c].commit_ts)
       ELSE UNCHANGED key_vars
    /\ UNCHANGED <<next_ts, client_state, client_ts>>

Abort(c) ==
    /\ client_state[c] \in {"working", "prewriting"}
    /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
    /\ UNCHANGED <<next_ts, client_ts, client_key, key_vars>>

Done ==
    /\ \A c \in CLIENT : client_state[c] \in {"committed", "aborted"}
    /\ UNCHANGED vars

Next ==
    \/ \E c \in CLIENT :
         \/ Start(c)
         \/ StartPrewrite(c)
         \/ StartCommit(c)
         \/ CommitPrimary(c)
         \/ Abort(c)
         \/ \E k \in KEY :
              \/ Get(c, k)
              \/ Cleanup(c, k)
              \/ Prewrite(c, k)
              \/ CommitSecondary(c, k)
    \/ Done

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Safety properties

\* Committed writes on a key are strictly ordered by commit ts, and each
\* commit ts is greater than its start ts.
WriteConsistency ==
    \A k \in KEY :
        /\ \A i \in DOMAIN key_write[k] :
             key_write[k][i].type = "write" =>
                 key_write[k][i].start_ts < key_write[k][i].ts
        /\ \A i, j \in DOMAIN key_write[k] :
             (/\ i < j
              /\ key_write[k][i].type = "write"
              /\ key_write[k][j].type = "write")
             => key_write[k][i].ts < key_write[k][j].ts

\* At most one lock per key; a lock has its data and is not yet resolved.
LockConsistency ==
    \A k \in KEY :
        /\ Cardinality(key_lock[k]) <= 1
        /\ \A l \in key_lock[k] :
             /\ [ts |-> l.ts] \in key_data[k]
             /\ ~hasCommit(k, l.ts)
             /\ ~hasRollback(k, l.ts)

\* A committed transaction has its primary committed, and every key it
\* wrote is either committed or still locked (to be rolled forward).
CommittedConsistency ==
    \A c \in CLIENT :
        LET s == client_ts[c].start_ts
            t == client_ts[c].commit_ts
            p == CLIENT_PRIMARY[c]
        IN client_state[c] = "committed" =>
             /\ \E w \in WritesOf(p) :
                  w.type = "write" /\ w.start_ts = s /\ w.ts = t
             /\ \A k \in CLIENT_KEY[c] :
                  /\ \/ hasLockEQ(k, s)
                     \/ \E w \in WritesOf(k) :
                          w.type = "write" /\ w.start_ts = s /\ w.ts = t
                  /\ ~hasRollback(k, s)

\* An aborted transaction never has its primary committed.
AbortedConsistency ==
    \A c \in CLIENT :
        client_state[c] = "aborted" =>
            ~hasCommit(CLIENT_PRIMARY[c], client_ts[c].start_ts)

\* A rolled-back transaction leaves no commit, lock, or data on that key, and
\* no key of a transaction whose primary committed is ever rolled back.
RollbackConsistency ==
    /\ \A k \in KEY : \A w \in WritesOf(k) :
         w.type = "rollback" =>
             /\ ~hasCommit(k, w.start_ts)
             /\ ~hasLockEQ(k, w.start_ts)
             /\ [ts |-> w.start_ts] \notin key_data[k]
    /\ \A c \in CLIENT :
         LET s == client_ts[c].start_ts IN
           (s # NoneTs /\ hasCommit(CLIENT_PRIMARY[c], s)) =>
               \A k \in CLIENT_KEY[c] : ~hasRollback(k, s)

\* The snapshot-isolation indicator is never falsified.
SnapshotIsolation == \A k \in KEY : key_si[k]

THEOREM Spec => [](TypeOK /\ WriteConsistency /\ LockConsistency
                   /\ CommittedConsistency /\ AbortedConsistency
                   /\ RollbackConsistency /\ SnapshotIsolation)
=============================================================================