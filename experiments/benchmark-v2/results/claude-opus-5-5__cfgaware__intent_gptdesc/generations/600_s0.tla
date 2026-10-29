------------------------------ MODULE Percolator ------------------------------
EXTENDS Integers, FiniteSets, Sequences, TLC

(***************************************************************************)
(* A model of a Percolator-style transactional key-value store with       *)
(* optimistic two-phase commit and timestamp ordering.  Each client runs  *)
(* one transaction that writes every key: the primary key first, then the *)
(* secondaries.  A timestamp oracle hands out unique, increasing start    *)
(* and commit timestamps.  Any lock may be resolved concurrently, either  *)
(* by rolling it forward or by rolling it back.                           *)
(***************************************************************************)

CONSTANTS c1, c2, c3

\* The set of keys in the store.
CONSTANTS KEY

\* The set of clients that issue transactions.
CONSTANTS CLIENT

\* A function mapping each client to the primary key of its transaction.
CONSTANTS CLIENT_PRIMARY_KEY

-----------------------------------------------------------------------------
\* Concrete values for the model.
\* c1 and c2 share a primary key, so they are symmetric.

Key == {"k1", "k2"}

Client == {c1, c2, c3}

ClientPrimaryKey == [c \in Client |-> IF c = c3 THEN "k2" ELSE "k1"]

Symmetry == Permutations({c1, c2})

-----------------------------------------------------------------------------
\* next_ts         : the timestamp oracle (monotonically increasing).
\* client_state[c] : the phase of client c's transaction.
\* client_ts[c]    : [start_ts, commit_ts] of client c's transaction.
\* client_key[c]   : [primary, secondary, pending], where pending holds the
\*                   keys still to be prewritten.
\* key_lock[k]     : the set of locks on k (at most one element).
\* key_write[k]    : the sequence of commit ("write") and "rollback" records.
\* key_data[k]     : the set of start timestamps of data versions of k.
VARIABLES next_ts, client_state, client_ts, client_key,
          key_lock, key_write, key_data

vars == <<next_ts, client_state, client_ts, client_key,
          key_lock, key_write, key_data>>

TS == 0 .. (2 * Cardinality(CLIENT) + 1)

States == {"init", "prewriting", "committing", "committed", "aborted"}

LockRec  == [ts : TS, primary : KEY]
WriteRec == [ts : TS, start_ts : TS, type : {"write", "rollback"}]

WritesOf(k) == {key_write[k][i] : i \in DOMAIN key_write[k]}

\* A key can be locked by a transaction that started at start only if two
\* conditions hold.  First, no lock is currently held on the key.  Second,
\* no commit or rollback record exists at or after start.  The second
\* condition gives first-committer-wins.
CanLock(k, start) ==
    /\ key_lock[k] = {}
    /\ \A w \in WritesOf(k) : w.ts < start

-----------------------------------------------------------------------------
Init ==
    /\ next_ts = 1
    /\ client_state = [c \in CLIENT |-> "init"]
    /\ client_ts = [c \in CLIENT |-> [start_ts |-> 0, commit_ts |-> 0]]
    /\ client_key = [c \in CLIENT |->
                        [primary   |-> CLIENT_PRIMARY_KEY[c],
                         secondary |-> KEY \ {CLIENT_PRIMARY_KEY[c]},
                         pending   |-> {}]]
    /\ key_lock = [k \in KEY |-> {}]
    /\ key_write = [k \in KEY |-> <<>>]
    /\ key_data = [k \in KEY |-> {}]

\* The client obtains a start timestamp and begins its transaction.
Start(c) ==
    /\ client_state[c] = "init"
    /\ next_ts' = next_ts + 1
    /\ client_ts' = [client_ts EXCEPT ![c].start_ts = next_ts]
    /\ client_key' = [client_key EXCEPT ![c].pending = KEY]
    /\ client_state' = [client_state EXCEPT ![c] = "prewriting"]
    /\ UNCHANGED <<key_lock, key_write, key_data>>

\* Prewrite one pending key, primary first.  If the key cannot be locked,
\* the transaction aborts.  Its leftover locks are cleaned up later by
\* ResolveLock.
Prewrite(c) ==
    /\ client_state[c] = "prewriting"
    /\ client_key[c].pending # {}
    /\ LET start == client_ts[c].start_ts
           pri   == client_key[c].primary
       IN \E k \in client_key[c].pending :
            /\ (pri \in client_key[c].pending) => (k = pri)
            /\ IF CanLock(k, start)
               THEN /\ key_lock' = [key_lock EXCEPT ![k] =
                                      {[ts |-> start, primary |-> pri]}]
                    /\ key_data' = [key_data EXCEPT ![k] = @ \cup {start}]
                    /\ client_key' = [client_key EXCEPT ![c].pending = @ \ {k}]
                    /\ UNCHANGED <<next_ts, client_state, client_ts, key_write>>
               ELSE /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
                    /\ UNCHANGED <<next_ts, client_ts, client_key,
                                   key_lock, key_write, key_data>>

\* After every key is prewritten, the client obtains a commit timestamp.
GetCommitTs(c) ==
    /\ client_state[c] = "prewriting"
    /\ client_key[c].pending = {}
    /\ next_ts' = next_ts + 1
    /\ client_ts' = [client_ts EXCEPT ![c].commit_ts = next_ts]
    /\ client_state' = [client_state EXCEPT ![c] = "committing"]
    /\ UNCHANGED <<client_key, key_lock, key_write, key_data>>

\* Committing the primary key is the atomic commit point.  If the primary
\* lock has been rolled back by a concurrent resolver, the client aborts.
CommitPrimary(c) ==
    /\ client_state[c] = "committing"
    /\ LET p     == client_key[c].primary
           start == client_ts[c].start_ts
           cts   == client_ts[c].commit_ts
       IN IF \E l \in key_lock[p] : l.ts = start
          THEN /\ key_lock' = [key_lock EXCEPT ![p] = {}]
               /\ key_write' = [key_write EXCEPT ![p] =
                     Append(@, [ts |-> cts, start_ts |-> start, type |-> "write"])]
               /\ client_state' = [client_state EXCEPT ![c] = "committed"]
               /\ UNCHANGED <<next_ts, client_ts, client_key, key_data>>
          ELSE /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
               /\ UNCHANGED <<next_ts, client_ts, client_key,
                              key_lock, key_write, key_data>>

\* Secondary keys are committed asynchronously after the primary commits.
CommitSecondary(c) ==
    /\ client_state[c] = "committed"
    /\ LET start == client_ts[c].start_ts
           cts   == client_ts[c].commit_ts
       IN \E k \in client_key[c].secondary :
            /\ \E l \in key_lock[k] : l.ts = start
            /\ key_lock' = [key_lock EXCEPT ![k] = {}]
            /\ key_write' = [key_write EXCEPT ![k] =
                  Append(@, [ts |-> cts, start_ts |-> start, type |-> "write"])]
    /\ UNCHANGED <<next_ts, client_state, client_ts, client_key, key_data>>

\* Concurrent lock resolution.  The outcome depends on the primary key:
\*  - if the primary has a commit record, the lock is rolled forward;
\*  - if the lock is on the primary itself, it may be rolled back;
\*  - if the lock is on a secondary and the primary is neither locked nor
\*    committed, the lock is rolled back.
ResolveLock(k) ==
    /\ \E l \in key_lock[k] :
        LET p  == l.primary
            cw == {w \in WritesOf(p) : w.start_ts = l.ts /\ w.type = "write"}
            Rollback ==
                /\ key_lock' = [key_lock EXCEPT ![k] = {}]
                /\ key_data' = [key_data EXCEPT ![k] = @ \ {l.ts}]
                /\ key_write' = [key_write EXCEPT ![k] =
                      Append(@, [ts |-> l.ts, start_ts |-> l.ts, type |-> "rollback"])]
        IN IF cw # {}
           THEN /\ key_lock' = [key_lock EXCEPT ![k] = {}]
                /\ key_write' = [key_write EXCEPT ![k] =
                      Append(@, [ts |-> (CHOOSE w \in cw : TRUE).ts,
                                 start_ts |-> l.ts, type |-> "write"])]
                /\ UNCHANGED key_data
           ELSE IF k = p
                THEN Rollback
                ELSE /\ ~(\E pl \in key_lock[p] : pl.ts = l.ts)
                     /\ Rollback
    /\ UNCHANGED <<next_ts, client_state, client_ts, client_key>>

\* Terminal stuttering once every transaction is finished and no lock remains.
Done ==
    /\ \A c \in CLIENT : client_state[c] \in {"committed", "aborted"}
    /\ \A k \in KEY : key_lock[k] = {}
    /\ UNCHANGED vars

Next ==
    \/ \E c \in CLIENT :
          \/ Start(c)
          \/ Prewrite(c)
          \/ GetCommitTs(c)
          \/ CommitPrimary(c)
          \/ CommitSecondary(c)
    \/ \E k \in KEY : ResolveLock(k)
    \/ Done

Fairness ==
    /\ \A c \in CLIENT : WF_vars(Start(c) \/ Prewrite(c) \/ GetCommitTs(c)
                                 \/ CommitPrimary(c) \/ CommitSecondary(c))
    /\ \A k \in KEY : WF_vars(ResolveLock(k))

PercolatorSpec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Invariants

TypeInvariant ==
    /\ next_ts \in TS
    /\ client_state \in [CLIENT -> States]
    /\ client_ts \in [CLIENT -> [start_ts : TS, commit_ts : TS]]
    /\ client_key \in [CLIENT -> [primary : KEY, secondary : SUBSET KEY,
                                  pending : SUBSET KEY]]
    /\ key_lock \in [KEY -> SUBSET LockRec]
    /\ key_data \in [KEY -> SUBSET TS]
    /\ DOMAIN key_write = KEY
    /\ \A k \in KEY : \A i \in DOMAIN key_write[k] : key_write[k][i] \in WriteRec

\* Every commit record refers to an existing data version, and its commit
\* timestamp is later than its start timestamp.
WriteConsistency ==
    \A k \in KEY : \A w \in WritesOf(k) :
        w.type = "write" => (w.start_ts < w.ts /\ w.start_ts \in key_data[k])

\* Each key holds at most one lock.
\* Every lock has data, and no commit or rollback record exists for it yet.
\* The primary of a secondary lock is either locked or decided.
LockConsistency ==
    \A k \in KEY :
        /\ Cardinality(key_lock[k]) <= 1
        /\ \A l \in key_lock[k] :
            /\ l.ts \in key_data[k]
            /\ \A w \in WritesOf(k) : w.start_ts # l.ts
            /\ k # l.primary =>
                 \/ \E pl \in key_lock[l.primary] : pl.ts = l.ts
                 \/ \E w \in WritesOf(l.primary) : w.start_ts = l.ts

\* For a committed transaction, the primary is committed.
\* Every secondary is either committed or still locked, pending roll-forward.
\* No key holds a rollback record for the transaction (atomicity).
CommittedConsistency ==
    \A c \in CLIENT : client_state[c] = "committed" =>
        LET s   == client_ts[c].start_ts
            cts == client_ts[c].commit_ts
            p   == client_key[c].primary
            rec == [ts |-> cts, start_ts |-> s, type |-> "write"]
        IN /\ rec \in WritesOf(p)
           /\ \A k \in client_key[c].secondary :
                 \/ \E l \in key_lock[k] : l.ts = s
                 \/ rec \in WritesOf(k)
           /\ \A k \in KEY :
                 [ts |-> s, start_ts |-> s, type |-> "rollback"] \notin WritesOf(k)

\* An aborted transaction never has any of its writes committed.
AbortedConsistency ==
    \A c \in CLIENT : client_state[c] = "aborted" =>
        \A k \in KEY : \A w \in WritesOf(k) :
            ~(w.type = "write" /\ w.start_ts = client_ts[c].start_ts)

\* A rolled-back transaction has no commit record on any key (no partial commit).
RollbackConsistency ==
    \A k \in KEY : \A w \in WritesOf(k) :
        w.type = "rollback" =>
            \A k2 \in KEY : \A w2 \in WritesOf(k2) :
                ~(w2.type = "write" /\ w2.start_ts = w.start_ts)

\* Each transaction writes at most one record per key, and timestamps are unique.
UniqueWrite ==
    \A k \in KEY : \A i, j \in DOMAIN key_write[k] :
        i # j => /\ key_write[k][i].start_ts # key_write[k][j].start_ts
                 /\ key_write[k][i].ts # key_write[k][j].ts

\* No write-write conflict: the [start, commit] intervals of committed
\* writes to the same key never overlap (first committer wins).
SnapshotIsolation ==
    \A k \in KEY : \A w1, w2 \in WritesOf(k) :
        (w1.type = "write" /\ w2.type = "write" /\ w1 # w2) =>
            (w1.ts < w2.start_ts \/ w2.ts < w1.start_ts)

\* Liveness: every transaction eventually finishes and all locks are resolved.
Progress ==
    <>(/\ \A c \in CLIENT : client_state[c] \in {"committed", "aborted"}
       /\ \A k \in KEY : key_lock[k] = {})

=============================================================================