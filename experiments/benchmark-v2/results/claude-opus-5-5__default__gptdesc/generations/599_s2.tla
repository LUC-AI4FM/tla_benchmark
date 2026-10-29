---------------------------- MODULE OptimizedPercolator ----------------------------
EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS KEY,            \* The set of keys
          CLIENT,         \* The set of clients (transactions)
          CLIENT_PRIMARY, \* CLIENT_PRIMARY[c] is the primary key of client c
          CLIENT_KEY      \* CLIENT_KEY[c] is the set of keys client c touches

ASSUME CLIENT_KEY \in [CLIENT -> SUBSET KEY]
ASSUME CLIENT_PRIMARY \in [CLIENT -> KEY]
ASSUME \A c \in CLIENT : CLIENT_PRIMARY[c] \in CLIENT_KEY[c]

VARIABLES next_ts,       \* Timestamp oracle
          client_state,  \* State of each client
          client_ts,     \* Start and commit timestamps of each client
          client_key,    \* Primary, secondary and pending keys of each client
          key_lock,      \* Locks on each key
          key_write,     \* Write / rollback records of each key (ordered)
          key_data,      \* Versioned data of each key (indexed by start_ts)
          key_si         \* Snapshot isolation indicator for each key

client_vars == <<client_state, client_ts, client_key>>
key_vars    == <<key_lock, key_write, key_data, key_si>>
vars        == <<next_ts, client_vars, key_vars>>

States == {"init", "working", "prewriting", "committing", "committed", "aborted"}

-----------------------------------------------------------------------------------
\* Helpers

writesOf(k) == {key_write[k][i] : i \in DOMAIN key_write[k]}

findWriteWithStartTS(k, ts) == {w \in writesOf(k) : w.start_ts = ts}

findCommitWithStartTS(k, ts) ==
    {w \in findWriteWithStartTS(k, ts) : w.type = "write"}

findRollbackWithStartTS(k, ts) ==
    {w \in findWriteWithStartTS(k, ts) : w.type = "rollback"}

hasLockEQ(k, ts) == \E l \in key_lock[k] : l.ts = ts

hasLockLE(k, ts) == \E l \in key_lock[k] : l.ts <= ts

hasStaleLock(k, ts) == \E l \in key_lock[k] : l.ts < ts

\* A key can be locked by a transaction with start timestamp ts only if it has
\* no lock and there is no write/rollback record with timestamp >= ts.
canLockKey(k, ts) ==
    /\ key_lock[k] = {}
    /\ ~\E w \in writesOf(k) : w.ts >= ts

\* Snapshot isolation check: committing a write on k for a transaction with
\* start_ts s and commit_ts t must not overlap with another committed write.
siOK(k, s, t) ==
    ~\E w \in writesOf(k) :
        /\ w.type = "write"
        /\ w.start_ts # s
        /\ w.start_ts < t
        /\ s < w.ts

\* Roll back key k for the transaction with start timestamp s.
rollbackKey(k, s) ==
    /\ key_lock' = [key_lock EXCEPT ![k] = {l \in @ : l.ts # s}]
    /\ key_write' = [key_write EXCEPT ![k] =
                        Append(@, [ts |-> s, start_ts |-> s, type |-> "rollback"])]
    /\ key_data' = [key_data EXCEPT ![k] = @ \ {s}]
    /\ UNCHANGED key_si

\* Commit (roll forward) key k for the transaction with start s, commit t.
commitKey(k, s, t) ==
    /\ key_lock' = [key_lock EXCEPT ![k] = {l \in @ : l.ts # s}]
    /\ key_write' = [key_write EXCEPT ![k] =
                        Append(@, [ts |-> t, start_ts |-> s, type |-> "write"])]
    /\ key_si' = [key_si EXCEPT ![k] = @ /\ siOK(k, s, t)]
    /\ UNCHANGED key_data

\* Resolve stale lock l found on key k.
cleanupStaleLock(k, l) ==
    LET p == l.primary
        s == l.ts
    IN
    IF hasLockEQ(p, s)
    THEN rollbackKey(p, s)                       \* primary still locked: roll back primary
    ELSE IF findCommitWithStartTS(p, s) # {}
         THEN \E w \in findCommitWithStartTS(p, s) :
                 commitKey(k, s, w.ts)           \* primary committed: roll forward
         ELSE rollbackKey(k, s)                  \* primary rolled back: roll back

-----------------------------------------------------------------------------------
Init ==
    /\ next_ts = 1
    /\ client_state = [c \in CLIENT |-> "init"]
    /\ client_ts = [c \in CLIENT |-> [start_ts |-> 0, commit_ts |-> 0]]
    /\ client_key = [c \in CLIENT |->
                        [primary   |-> CLIENT_PRIMARY[c],
                         secondary |-> CLIENT_KEY[c] \ {CLIENT_PRIMARY[c]},
                         pending   |-> {}]]
    /\ key_lock = [k \in KEY |-> {}]
    /\ key_write = [k \in KEY |-> <<>>]
    /\ key_data = [k \in KEY |-> {}]
    /\ key_si = [k \in KEY |-> TRUE]

\* Client obtains a start timestamp.
Start(c) ==
    /\ client_state[c] = "init"
    /\ next_ts' = next_ts + 1
    /\ client_state' = [client_state EXCEPT ![c] = "working"]
    /\ client_ts' = [client_ts EXCEPT ![c].start_ts = next_ts]
    /\ UNCHANGED <<client_key, key_vars>>

\* Client reads its keys (no lock with ts <= start_ts blocks it), then
\* begins prewriting.
Get(c) ==
    /\ client_state[c] = "working"
    /\ \A k \in CLIENT_KEY[c] : ~hasLockLE(k, client_ts[c].start_ts)
    /\ client_state' = [client_state EXCEPT ![c] = "prewriting"]
    /\ client_key' = [client_key EXCEPT ![c].pending = CLIENT_KEY[c]]
    /\ UNCHANGED <<next_ts, client_ts, key_vars>>

\* Client cleans up a stale lock that blocks its reads.
Cleanup(c) ==
    /\ client_state[c] = "working"
    /\ \E k \in CLIENT_KEY[c] :
         \E l \in key_lock[k] :
            /\ l.ts < client_ts[c].start_ts
            /\ cleanupStaleLock(k, l)
    /\ UNCHANGED <<next_ts, client_vars>>

\* Keys that may currently be prewritten: primary first, then secondaries.
prewriteCandidates(c) ==
    IF client_key[c].primary \in client_key[c].pending
    THEN {client_key[c].primary}
    ELSE client_key[c].pending

\* Client prewrites (locks) one of its pending keys.
Prewrite(c) ==
    /\ client_state[c] = "prewriting"
    /\ \E k \in prewriteCandidates(c) :
         LET s == client_ts[c].start_ts
             newPending == client_key[c].pending \ {k}
         IN
         /\ canLockKey(k, s)
         /\ key_lock' = [key_lock EXCEPT ![k] =
                           @ \cup {[ts |-> s, primary |-> client_key[c].primary]}]
         /\ key_data' = [key_data EXCEPT ![k] = @ \cup {s}]
         /\ client_key' = [client_key EXCEPT ![c].pending = newPending]
         /\ client_state' = [client_state EXCEPT ![c] =
                               IF newPending = {} THEN "committing" ELSE "prewriting"]
    /\ UNCHANGED <<next_ts, client_ts, key_write, key_si>>

\* Client commits its primary key; secondaries are resolved lazily.
Commit(c) ==
    /\ client_state[c] = "committing"
    /\ LET p == client_key[c].primary
           s == client_ts[c].start_ts
       IN
       /\ hasLockEQ(p, s)
       /\ next_ts' = next_ts + 1
       /\ client_ts' = [client_ts EXCEPT ![c].commit_ts = next_ts]
       /\ client_state' = [client_state EXCEPT ![c] = "committed"]
       /\ commitKey(p, s, next_ts)
    /\ UNCHANGED client_key

\* Client aborts: either a key cannot be locked, or the primary lock was lost.
Abort(c) ==
    /\ \/ /\ client_state[c] = "prewriting"
          /\ \E k \in prewriteCandidates(c) :
                ~canLockKey(k, client_ts[c].start_ts)
       \/ /\ client_state[c] = "committing"
          /\ ~hasLockEQ(client_key[c].primary, client_ts[c].start_ts)
    /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
    /\ client_key' = [client_key EXCEPT ![c].pending = {}]
    /\ UNCHANGED <<next_ts, client_ts, key_vars>>

Next ==
    \E c \in CLIENT :
        \/ Start(c)
        \/ Get(c)
        \/ Cleanup(c)
        \/ Prewrite(c)
        \/ Commit(c)
        \/ Abort(c)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------------
\* Invariants

TypeOK ==
    /\ next_ts \in Nat
    /\ client_state \in [CLIENT -> States]
    /\ client_ts \in [CLIENT -> [start_ts : Nat, commit_ts : Nat]]
    /\ client_key \in [CLIENT -> [primary : KEY,
                                  secondary : SUBSET KEY,
                                  pending : SUBSET KEY]]
    /\ key_lock \in [KEY -> SUBSET [ts : Nat, primary : KEY]]
    /\ key_write \in [KEY -> Seq([ts : Nat, start_ts : Nat,
                                  type : {"write", "rollback"}])]
    /\ key_data \in [KEY -> SUBSET Nat]
    /\ key_si \in [KEY -> BOOLEAN]

\* Committed writes on a key appear in strictly increasing commit-ts order,
\* and each commit ts is greater than its start ts.
WriteConsistency ==
    \A k \in KEY :
        /\ \A i \in DOMAIN key_write[k] :
              key_write[k][i].type = "write" =>
                  key_write[k][i].start_ts < key_write[k][i].ts
        /\ \A i, j \in DOMAIN key_write[k] :
              /\ i < j
              /\ key_write[k][i].type = "write"
              /\ key_write[k][j].type = "write"
              => key_write[k][i].ts < key_write[k][j].ts

\* At most one lock per key; a locked version has no write/rollback record;
\* a secondary lock implies its primary was locked.
LockConsistency ==
    \A k \in KEY :
        /\ Cardinality(key_lock[k]) <= 1
        /\ \A l \in key_lock[k] :
              /\ findWriteWithStartTS(k, l.ts) = {}
              /\ l.ts \in key_data[k]
              /\ \/ hasLockEQ(l.primary, l.ts)
                 \/ findWriteWithStartTS(l.primary, l.ts) # {}

\* A committed client has committed its primary at its commit ts, and every
\* secondary is either still locked or committed.
CommittedConsistency ==
    \A c \in CLIENT :
        LET s == client_ts[c].start_ts
            t == client_ts[c].commit_ts
            p == client_key[c].primary
        IN
        client_state[c] = "committed" =>
            /\ [ts |-> t, start_ts |-> s, type |-> "write"] \in writesOf(p)
            /\ \A k \in client_key[c].secondary :
                  \/ hasLockEQ(k, s)
                  \/ [ts |-> t, start_ts |-> s, type |-> "write"] \in writesOf(k)

\* An aborted client never has any committed write.
AbortedConsistency ==
    \A c \in CLIENT :
        client_state[c] = "aborted" =>
            \A k \in CLIENT_KEY[c] :
                findCommitWithStartTS(k, client_ts[c].start_ts) = {}

\* A transaction is never both rolled back and committed on any keys.
RollbackConsistency ==
    \A c \in CLIENT :
        LET s == client_ts[c].start_ts
        IN
        s # 0 =>
            ~\E k1, k2 \in CLIENT_KEY[c] :
                /\ findCommitWithStartTS(k1, s) # {}
                /\ findRollbackWithStartTS(k2, s) # {}

\* Snapshot isolation indicator is preserved.
SnapshotIsolation == \A k \in KEY : key_si[k]

THEOREM Spec => [](TypeOK /\ WriteConsistency /\ LockConsistency
                   /\ CommittedConsistency /\ AbortedConsistency
                   /\ RollbackConsistency /\ SnapshotIsolation)
===================================================================================