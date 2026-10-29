------------------------------- MODULE Percolator -------------------------------
EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS
    CLIENT,          \* set of clients (transactions)
    KEY,             \* set of keys
    CLIENT_KEY,      \* CLIENT_KEY[c] : the set of keys client c writes
    CLIENT_PRIMARY   \* CLIENT_PRIMARY[c] : the primary key of client c

ASSUME /\ CLIENT_KEY \in [CLIENT -> SUBSET KEY]
       /\ CLIENT_PRIMARY \in [CLIENT -> KEY]
       /\ \A c \in CLIENT : CLIENT_PRIMARY[c] \in CLIENT_KEY[c]

VARIABLES
    next_ts,        \* timestamp oracle
    client_state,   \* state of each client
    client_ts,      \* [start_ts, commit_ts] of each client
    client_key,     \* [primary, secondary, pending] of each client
    key_lock,       \* key_lock[k] : set of locks on key k
    key_write,      \* key_write[k] : sequence of write / rollback records
    key_data,       \* key_data[k] : set of start_ts with data written
    key_si          \* key_si[k] : snapshot isolation indicator for key k

client_vars == <<client_state, client_ts, client_key>>
key_vars    == <<key_lock, key_write, key_data, key_si>>
vars        == <<next_ts, client_vars, key_vars>>

States == {"init", "working", "prewriting", "committing", "committed", "aborted"}

LockType  == [ts : Nat, primary : KEY]
WriteType == [ts : Nat, start_ts : Nat, type : {"write", "rollback"}]

-----------------------------------------------------------------------------
\* Helpers

writes(k) == {key_write[k][i] : i \in DOMAIN key_write[k]}

findWrite(k, s) == {w \in writes(k) : w.start_ts = s}

hasLockTs(k, s) == \E l \in key_lock[k] : l.ts = s

\* A key can be locked by a transaction with start ts "ts" iff there is
\* no lock on it and there is no write/rollback record at or after ts.
canLock(k, ts) ==
    /\ key_lock[k] = {}
    /\ ~\E w \in writes(k) : w.ts >= ts

\* Roll back the transaction with start_ts s on key k.
RollbackKey(k, s) ==
    /\ key_lock'  = [key_lock  EXCEPT ![k] = {l \in @ : l.ts # s}]
    /\ key_data'  = [key_data  EXCEPT ![k] = @ \ {s}]
    /\ key_write' = [key_write EXCEPT ![k] =
                        Append(@, [ts |-> s, start_ts |-> s, type |-> "rollback"])]
    /\ UNCHANGED key_si

\* Commit the transaction with start_ts s and commit_ts c on key k.
CommitKey(k, s, c) ==
    /\ key_lock'  = [key_lock  EXCEPT ![k] = {l \in @ : l.ts # s}]
    /\ key_write' = [key_write EXCEPT ![k] =
                        Append(@, [ts |-> c, start_ts |-> s, type |-> "write"])]
    /\ key_si'    = [key_si EXCEPT ![k] =
                        @ /\ ~\E w \in writes(k) :
                                /\ w.type = "write"
                                /\ w.ts > s
                                /\ w.ts < c]
    /\ UNCHANGED key_data

-----------------------------------------------------------------------------
\* Initial state

Init ==
    /\ next_ts = 1
    /\ client_state = [c \in CLIENT |-> "init"]
    /\ client_ts = [c \in CLIENT |-> [start_ts |-> 0, commit_ts |-> 0]]
    /\ client_key = [c \in CLIENT |->
                        [primary   |-> CLIENT_PRIMARY[c],
                         secondary |-> CLIENT_KEY[c] \ {CLIENT_PRIMARY[c]},
                         pending   |-> CLIENT_KEY[c]]]
    /\ key_lock  = [k \in KEY |-> {}]
    /\ key_write = [k \in KEY |-> <<>>]
    /\ key_data  = [k \in KEY |-> {}]
    /\ key_si    = [k \in KEY |-> TRUE]

-----------------------------------------------------------------------------
\* Client actions

\* Client obtains a start timestamp and begins working.
Start(c) ==
    /\ client_state[c] = "init"
    /\ client_state' = [client_state EXCEPT ![c] = "working"]
    /\ client_ts' = [client_ts EXCEPT ![c].start_ts = next_ts]
    /\ next_ts' = next_ts + 1
    /\ UNCHANGED <<client_key, key_vars>>

\* Client reads a key; only possible if no lock older than its start_ts blocks it.
ReadKey(c) ==
    /\ client_state[c] = "working"
    /\ \E k \in CLIENT_KEY[c] :
          ~\E l \in key_lock[k] : l.ts < client_ts[c].start_ts
    /\ UNCHANGED vars

\* Client cleans up a stale lock encountered on one of its keys.
CleanupStaleLock(c) ==
    /\ client_state[c] = "working"
    /\ \E k \in CLIENT_KEY[c] :
         \E l \in key_lock[k] :
           /\ l.ts < client_ts[c].start_ts
           /\ LET p == l.primary IN
                IF hasLockTs(p, l.ts)
                THEN \* primary still locked: roll back the primary
                     RollbackKey(p, l.ts)
                ELSE LET ws == findWrite(p, l.ts) IN
                     IF ws = {}
                     THEN RollbackKey(p, l.ts)
                     ELSE LET w == CHOOSE x \in ws : TRUE IN
                          IF w.type = "write"
                          THEN CommitKey(k, l.ts, w.ts)   \* roll forward
                          ELSE RollbackKey(k, l.ts)       \* roll back
    /\ UNCHANGED <<next_ts, client_vars>>

\* Client starts the prewrite phase.
StartPrewrite(c) ==
    /\ client_state[c] = "working"
    /\ client_state' = [client_state EXCEPT ![c] = "prewriting"]
    /\ UNCHANGED <<next_ts, client_ts, client_key, key_vars>>

\* Client prewrites (locks) a pending key; the primary is prewritten first.
Prewrite(c) ==
    /\ client_state[c] = "prewriting"
    /\ LET s == client_ts[c].start_ts
           p == client_key[c].primary IN
       \E k \in client_key[c].pending :
          /\ (k = p \/ p \notin client_key[c].pending)
          /\ canLock(k, s)
          /\ key_lock' = [key_lock EXCEPT ![k] = @ \cup {[ts |-> s, primary |-> p]}]
          /\ key_data' = [key_data EXCEPT ![k] = @ \cup {s}]
          /\ client_key' = [client_key EXCEPT ![c].pending = @ \ {k}]
    /\ UNCHANGED <<next_ts, client_state, client_ts, key_write, key_si>>

\* All keys prewritten: client obtains a commit timestamp.
StartCommit(c) ==
    /\ client_state[c] = "prewriting"
    /\ client_key[c].pending = {}
    /\ client_state' = [client_state EXCEPT ![c] = "committing"]
    /\ client_ts' = [client_ts EXCEPT ![c].commit_ts = next_ts]
    /\ next_ts' = next_ts + 1
    /\ UNCHANGED <<client_key, key_vars>>

\* Client commits the primary key; this is the commit point of the transaction.
CommitPrimary(c) ==
    /\ client_state[c] = "committing"
    /\ hasLockTs(client_key[c].primary, client_ts[c].start_ts)
    /\ CommitKey(client_key[c].primary, client_ts[c].start_ts, client_ts[c].commit_ts)
    /\ client_state' = [client_state EXCEPT ![c] = "committed"]
    /\ UNCHANGED <<next_ts, client_ts, client_key>>

\* After the primary is committed, secondaries are committed asynchronously.
CommitSecondary(c) ==
    /\ client_state[c] = "committed"
    /\ \E k \in client_key[c].secondary :
          /\ hasLockTs(k, client_ts[c].start_ts)
          /\ CommitKey(k, client_ts[c].start_ts, client_ts[c].commit_ts)
    /\ UNCHANGED <<next_ts, client_vars>>

\* Client aborts.
Abort(c) ==
    /\ \/ client_state[c] = "working"
       \/ /\ client_state[c] = "prewriting"
          /\ \E k \in client_key[c].pending :
                /\ (k = client_key[c].primary \/ client_key[c].primary \notin client_key[c].pending)
                /\ ~canLock(k, client_ts[c].start_ts)
       \/ /\ client_state[c] = "committing"
          /\ ~hasLockTs(client_key[c].primary, client_ts[c].start_ts)
    /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
    /\ UNCHANGED <<next_ts, client_ts, client_key, key_vars>>

-----------------------------------------------------------------------------

Next ==
    \E c \in CLIENT :
        \/ Start(c)
        \/ ReadKey(c)
        \/ CleanupStaleLock(c)
        \/ StartPrewrite(c)
        \/ Prewrite(c)
        \/ StartCommit(c)
        \/ CommitPrimary(c)
        \/ CommitSecondary(c)
        \/ Abort(c)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Invariants

TypeOK ==
    /\ next_ts \in Nat
    /\ client_state \in [CLIENT -> States]
    /\ \A c \in CLIENT :
          /\ client_ts[c].start_ts \in Nat
          /\ client_ts[c].commit_ts \in Nat
          /\ client_key[c].primary \in KEY
          /\ client_key[c].secondary \subseteq KEY
          /\ client_key[c].pending \subseteq KEY
    /\ \A k \in KEY :
          /\ \A l \in key_lock[k] : l \in LockType
          /\ \A i \in DOMAIN key_write[k] : key_write[k][i] \in WriteType
          /\ key_data[k] \subseteq Nat
          /\ key_si[k] \in BOOLEAN

\* Committed write records on each key appear in increasing commit-ts order,
\* and each commit ts is greater than its start ts.
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

\* At most one lock per key; a lock always has data and no commit/rollback record.
LockConsistency ==
    \A k \in KEY :
       /\ Cardinality(key_lock[k]) <= 1
       /\ \A l \in key_lock[k] :
             /\ l.ts \in key_data[k]
             /\ findWrite(k, l.ts) = {}

\* A committed transaction has its primary committed and every secondary
\* either still locked or committed with the same commit ts.
CommittedConsistency ==
    \A c \in CLIENT :
       client_state[c] = "committed" =>
          LET s == client_ts[c].start_ts
              t == client_ts[c].commit_ts IN
          /\ \E w \in findWrite(client_key[c].primary, s) :
                w.type = "write" /\ w.ts = t
          /\ \A k \in client_key[c].secondary :
                \/ hasLockTs(k, s)
                \/ \E w \in findWrite(k, s) : w.type = "write" /\ w.ts = t

\* An aborted transaction never has any committed write record.
AbortedConsistency ==
    \A c \in CLIENT :
       client_state[c] = "aborted" =>
          \A k \in KEY :
             ~\E w \in findWrite(k, client_ts[c].start_ts) : w.type = "write"

CommittedAbortedConsistency == CommittedConsistency /\ AbortedConsistency

\* No key has both a commit and a rollback record for the same transaction,
\* and a rolled-back primary means no key of that transaction is committed.
RollbackConsistency ==
    \A c \in CLIENT :
       LET s == client_ts[c].start_ts IN
       /\ \A k \in KEY :
             ~(/\ \E w \in findWrite(k, s) : w.type = "write"
               /\ \E w \in findWrite(k, s) : w.type = "rollback")
       /\ (\E w \in findWrite(client_key[c].primary, s) : w.type = "rollback")
             => \A k \in KEY :
                   ~\E w \in findWrite(k, s) : w.type = "write"

\* The snapshot isolation indicator is never violated.
SnapshotIsolation ==
    \A k \in KEY : key_si[k] = TRUE

=============================================================================