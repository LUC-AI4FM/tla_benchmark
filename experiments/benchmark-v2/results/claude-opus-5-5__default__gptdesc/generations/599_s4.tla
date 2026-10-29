------------------------------ MODULE OptimizedPercolator ------------------------------
EXTENDS Integers, Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    CLIENT,          \* set of clients (transactions)
    KEY,             \* set of keys
    CLIENT_PRIMARY,  \* CLIENT_PRIMARY[c] : the primary key of client c
    CLIENT_KEY       \* CLIENT_KEY[c]     : the set of keys client c writes

ASSUME /\ CLIENT_PRIMARY \in [CLIENT -> KEY]
       /\ CLIENT_KEY \in [CLIENT -> SUBSET KEY]
       /\ \A c \in CLIENT : CLIENT_PRIMARY[c] \in CLIENT_KEY[c]

VARIABLES
    next_ts,        \* timestamp oracle
    client_state,   \* state of each client
    client_ts,      \* start_ts and commit_ts of each client
    client_key,     \* primary / secondary / pending keys of each client
    client_read,    \* version (start_ts of writer) last read by client per key; 0 = none
    key_lock,       \* per-key lock set (at most one lock)
    key_data,       \* per-key set of data versions (identified by start_ts)
    key_write,      \* per-key sequence of write / rollback records
    key_si          \* per-key snapshot isolation indicator

vars == << next_ts, client_state, client_ts, client_key, client_read,
           key_lock, key_data, key_write, key_si >>

-----------------------------------------------------------------------------------------
\* Helpers

ClientStates == {"init", "working", "prewriting", "committing", "committed", "aborted"}

LockRec  == [ts : Nat, primary : KEY]
WriteRec == [ts : Nat, start_ts : Nat, type : {"write", "rollback"}]

SeqToSet(s) == { s[i] : i \in DOMAIN s }

Writes(k) == SeqToSet(key_write[k])

StartTs(c)  == client_ts[c].start_ts
CommitTs(c) == client_ts[c].commit_ts

\* A key can be locked by a transaction with start timestamp ts iff it is not
\* locked and there is no write / rollback record with a timestamp >= ts.
CanLock(k, ts) ==
    /\ key_lock[k] = {}
    /\ ~ \E w \in Writes(k) : w.ts >= ts

\* Is key k locked by the transaction with start timestamp ts?
LockedBy(k, ts) == \E l \in key_lock[k] : l.ts = ts

\* Would committing a write on k for a transaction with start ts break SI?
SIConflict(k, start) ==
    \E w \in Writes(k) : w.type = "write" /\ w.ts > start

\* Latest committed version visible at ts (start_ts of writer, 0 if none)
VisibleVersion(k, ts) ==
    LET ws == { w \in Writes(k) : w.type = "write" /\ w.ts <= ts }
    IN  IF ws = {} THEN 0
        ELSE (CHOOSE w \in ws : \A w2 \in ws : w2.ts <= w.ts).start_ts

-----------------------------------------------------------------------------------------
\* Initial state

Init ==
    /\ next_ts = 1
    /\ client_state = [c \in CLIENT |-> "init"]
    /\ client_ts = [c \in CLIENT |-> [start_ts |-> 0, commit_ts |-> 0]]
    /\ client_key = [c \in CLIENT |->
                        [primary   |-> CLIENT_PRIMARY[c],
                         secondary |-> CLIENT_KEY[c] \ {CLIENT_PRIMARY[c]},
                         pending   |-> {}]]
    /\ client_read = [c \in CLIENT |-> [k \in KEY |-> 0]]
    /\ key_lock  = [k \in KEY |-> {}]
    /\ key_data  = [k \in KEY |-> {}]
    /\ key_write = [k \in KEY |-> << >>]
    /\ key_si    = [k \in KEY |-> TRUE]

-----------------------------------------------------------------------------------------
\* Client actions

\* Acquire a start timestamp and begin working.
Start(c) ==
    /\ client_state[c] = "init"
    /\ client_state' = [client_state EXCEPT ![c] = "working"]
    /\ client_ts' = [client_ts EXCEPT ![c].start_ts = next_ts]
    /\ next_ts' = next_ts + 1
    /\ UNCHANGED << client_key, client_read, key_lock, key_data, key_write, key_si >>

\* Read a key: only possible if there is no lock older than the start timestamp.
Get(c, k) ==
    /\ client_state[c] = "working"
    /\ ~ \E l \in key_lock[k] : l.ts < StartTs(c)
    /\ client_read' = [client_read EXCEPT ![c][k] = VisibleVersion(k, StartTs(c))]
    /\ UNCHANGED << next_ts, client_state, client_ts, client_key,
                    key_lock, key_data, key_write, key_si >>

\* Cleanup case 1: a stale lock whose primary is still locked -> roll back primary.
CleanupRollbackPrimary(c, k) ==
    /\ client_state[c] = "working"
    /\ \E l \in key_lock[k] :
         /\ l.ts < StartTs(c)
         /\ LET p == l.primary
                s == l.ts
            IN  /\ LockedBy(p, s)
                /\ key_lock'  = [key_lock  EXCEPT ![p] = {}]
                /\ key_data'  = [key_data  EXCEPT ![p] = @ \ {s}]
                /\ key_write' = [key_write EXCEPT ![p] =
                                   Append(@, [ts |-> s, start_ts |-> s, type |-> "rollback"])]
    /\ UNCHANGED << next_ts, client_state, client_ts, client_key, client_read, key_si >>

\* Cleanup case 2: primary has been committed -> roll forward the secondary.
CleanupRollForward(c, k) ==
    /\ client_state[c] = "working"
    /\ \E l \in key_lock[k] :
         /\ l.ts < StartTs(c)
         /\ LET p == l.primary
                s == l.ts
            IN  /\ ~ LockedBy(p, s)
                /\ \E w \in Writes(p) :
                     /\ w.type = "write"
                     /\ w.start_ts = s
                     /\ key_lock'  = [key_lock  EXCEPT ![k] = {}]
                     /\ key_write' = [key_write EXCEPT ![k] =
                                        Append(@, [ts |-> w.ts, start_ts |-> s, type |-> "write"])]
                     /\ key_si'    = [key_si EXCEPT ![k] = @ /\ ~ SIConflict(k, s)]
    /\ UNCHANGED << next_ts, client_state, client_ts, client_key, client_read, key_data >>

\* Cleanup case 3: primary has been rolled back -> roll back the secondary.
CleanupRollbackSecondary(c, k) ==
    /\ client_state[c] = "working"
    /\ \E l \in key_lock[k] :
         /\ l.ts < StartTs(c)
         /\ LET p == l.primary
                s == l.ts
            IN  /\ ~ LockedBy(p, s)
                /\ ~ \E w \in Writes(p) : w.type = "write" /\ w.start_ts = s
                /\ key_lock'  = [key_lock  EXCEPT ![k] = {}]
                /\ key_data'  = [key_data  EXCEPT ![k] = @ \ {s}]
                /\ key_write' = [key_write EXCEPT ![k] =
                                   Append(@, [ts |-> s, start_ts |-> s, type |-> "rollback"])]
    /\ UNCHANGED << next_ts, client_state, client_ts, client_key, client_read, key_si >>

\* Begin prewriting all keys of the transaction.
StartPrewrite(c) ==
    /\ client_state[c] = "working"
    /\ client_state' = [client_state EXCEPT ![c] = "prewriting"]
    /\ client_key' = [client_key EXCEPT ![c].pending = CLIENT_KEY[c]]
    /\ UNCHANGED << next_ts, client_ts, client_read, key_lock, key_data, key_write, key_si >>

\* Prewrite a key successfully (primary key must be prewritten first).
Prewrite(c, k) ==
    /\ client_state[c] = "prewriting"
    /\ k \in client_key[c].pending
    /\ (k = client_key[c].primary \/ client_key[c].primary \notin client_key[c].pending)
    /\ CanLock(k, StartTs(c))
    /\ key_lock' = [key_lock EXCEPT ![k] =
                      {[ts |-> StartTs(c), primary |-> client_key[c].primary]}]
    /\ key_data' = [key_data EXCEPT ![k] = @ \cup {StartTs(c)}]
    /\ client_key' = [client_key EXCEPT ![c].pending = @ \ {k}]
    /\ UNCHANGED << next_ts, client_state, client_ts, client_read, key_write, key_si >>

\* Prewrite fails due to a conflicting lock or newer write -> abort.
PrewriteFail(c, k) ==
    /\ client_state[c] = "prewriting"
    /\ k \in client_key[c].pending
    /\ (k = client_key[c].primary \/ client_key[c].primary \notin client_key[c].pending)
    /\ ~ CanLock(k, StartTs(c))
    /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
    /\ UNCHANGED << next_ts, client_ts, client_key, client_read,
                    key_lock, key_data, key_write, key_si >>

\* All keys prewritten: obtain a commit timestamp.
StartCommit(c) ==
    /\ client_state[c] = "prewriting"
    /\ client_key[c].pending = {}
    /\ client_state' = [client_state EXCEPT ![c] = "committing"]
    /\ client_ts' = [client_ts EXCEPT ![c].commit_ts = next_ts]
    /\ next_ts' = next_ts + 1
    /\ UNCHANGED << client_key, client_read, key_lock, key_data, key_write, key_si >>

\* Commit the primary key (optimized: secondaries are resolved lazily).
CommitPrimary(c) ==
    LET p == client_key[c].primary
        s == StartTs(c)
    IN  /\ client_state[c] = "committing"
        /\ LockedBy(p, s)
        /\ key_lock'  = [key_lock EXCEPT ![p] = {}]
        /\ key_write' = [key_write EXCEPT ![p] =
                           Append(@, [ts |-> CommitTs(c), start_ts |-> s, type |-> "write"])]
        /\ key_si'    = [key_si EXCEPT ![p] = @ /\ ~ SIConflict(p, s)]
        /\ client_state' = [client_state EXCEPT ![c] = "committed"]
        /\ UNCHANGED << next_ts, client_ts, client_key, client_read, key_data >>

\* Primary lock has been cleaned up by another client -> abort.
CommitPrimaryFail(c) ==
    LET p == client_key[c].primary
        s == StartTs(c)
    IN  /\ client_state[c] = "committing"
        /\ ~ LockedBy(p, s)
        /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
        /\ UNCHANGED << next_ts, client_ts, client_key, client_read,
                        key_lock, key_data, key_write, key_si >>

\* Client voluntarily aborts.
Abort(c) ==
    /\ client_state[c] \in {"working", "prewriting"}
    /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
    /\ UNCHANGED << next_ts, client_ts, client_key, client_read,
                    key_lock, key_data, key_write, key_si >>

\* All clients finished: allow stuttering to avoid spurious deadlock.
Terminating ==
    /\ \A c \in CLIENT : client_state[c] \in {"committed", "aborted"}
    /\ UNCHANGED vars

-----------------------------------------------------------------------------------------

Next ==
    \/ \E c \in CLIENT :
         \/ Start(c)
         \/ StartPrewrite(c)
         \/ StartCommit(c)
         \/ CommitPrimary(c)
         \/ CommitPrimaryFail(c)
         \/ Abort(c)
         \/ \E k \in KEY :
              \/ Get(c, k)
              \/ CleanupRollbackPrimary(c, k)
              \/ CleanupRollForward(c, k)
              \/ CleanupRollbackSecondary(c, k)
              \/ Prewrite(c, k)
              \/ PrewriteFail(c, k)
    \/ Terminating

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------------------
\* Invariants

TypeOK ==
    /\ next_ts \in Nat \ {0}
    /\ client_state \in [CLIENT -> ClientStates]
    /\ client_ts \in [CLIENT -> [start_ts : Nat, commit_ts : Nat]]
    /\ client_key \in [CLIENT -> [primary : KEY, secondary : SUBSET KEY, pending : SUBSET KEY]]
    /\ client_read \in [CLIENT -> [KEY -> Nat]]
    /\ key_lock \in [KEY -> SUBSET LockRec]
    /\ key_data \in [KEY -> SUBSET Nat]
    /\ key_write \in [KEY -> Seq(WriteRec)]
    /\ key_si \in [KEY -> BOOLEAN]

\* Write records on each key are strictly ordered by timestamp; commit
\* timestamps exceed start timestamps; rollback records use the start ts.
WriteConsistency ==
    \A k \in KEY :
        /\ \A i, j \in DOMAIN key_write[k] :
              i < j => key_write[k][i].ts < key_write[k][j].ts
        /\ \A w \in Writes(k) :
              /\ w.type = "write"    => (w.ts > w.start_ts /\ w.start_ts \in key_data[k])
              /\ w.type = "rollback" => w.ts = w.start_ts

\* At most one lock per key; a lock has data, no write record for its
\* transaction, and no write record at or after its timestamp.
LockConsistency ==
    \A k \in KEY :
        /\ Cardinality(key_lock[k]) <= 1
        /\ \A l \in key_lock[k] :
              /\ l.ts \in key_data[k]
              /\ \A w \in Writes(k) : w.start_ts # l.ts /\ w.ts < l.ts

\* A committed client has committed its primary, every secondary is either
\* still locked by it or committed with the same commit ts, and it has no
\* rollback records anywhere.
CommittedConsistency ==
    \A c \in CLIENT :
        client_state[c] = "committed" =>
            LET s   == StartTs(c)
                ct  == CommitTs(c)
                rec == [ts |-> ct, start_ts |-> s, type |-> "write"]
            IN  /\ rec \in Writes(client_key[c].primary)
                /\ \A k \in client_key[c].secondary :
                      LockedBy(k, s) \/ rec \in Writes(k)
                /\ \A k \in KEY :
                      ~ \E w \in Writes(k) : w.type = "rollback" /\ w.start_ts = s

\* An aborted client never has any committed write record.
AbortedConsistency ==
    \A c \in CLIENT :
        client_state[c] = "aborted" =>
            \A k \in KEY :
                ~ \E w \in Writes(k) : w.type = "write" /\ w.start_ts = StartTs(c)

\* A transaction that has been rolled back on some key is committed nowhere.
RollbackConsistency ==
    \A k \in KEY :
        \A w \in Writes(k) :
            w.type = "rollback" =>
                \A k2 \in KEY :
                    ~ \E w2 \in Writes(k2) : w2.type = "write" /\ w2.start_ts = w.start_ts

\* The snapshot isolation indicator is never violated.
SnapshotIsolation ==
    \A k \in KEY : key_si[k] = TRUE

Invariants ==
    /\ TypeOK
    /\ WriteConsistency
    /\ LockConsistency
    /\ CommittedConsistency
    /\ AbortedConsistency
    /\ RollbackConsistency
    /\ SnapshotIsolation

THEOREM Spec => []Invariants

=========================================================================================