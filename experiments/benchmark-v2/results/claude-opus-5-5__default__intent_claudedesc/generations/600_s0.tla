---------------------------- MODULE OptimizedCommitTS ----------------------------
(***************************************************************************)
(* Percolator-style distributed transaction protocol with an optimized    *)
(* commit timestamp mechanism, similar to "async commit".                 *)
(*                                                                         *)
(*  - Each key tracks the largest timestamp at which it has been read      *)
(*    (key_last_read_ts, i.e. "max_ts").                                   *)
(*  - Prewriting a key computes a lock-local min_commit_ts as              *)
(*    max(start_ts, key_last_read_ts) + 1. This guarantees that no         *)
(*    snapshot read that already happened can miss this write.             *)
(*  - Once every key of a transaction is locked (prewritten), the          *)
(*    transaction is logically committed. Its commit_ts is the maximum     *)
(*    min_commit_ts over all of its locks, so no extra round trip to the   *)
(*    timestamp oracle is needed.                                          *)
(*  - The primary key is the coordination point. The commit record is      *)
(*    written to the primary first, and secondaries are committed after.   *)
(*  - A reader that meets a foreign lock whose min_commit_ts <= read_ts    *)
(*    must wait. A lock with min_commit_ts > read_ts can be safely         *)
(*    ignored, because the final commit_ts is >= min_commit_ts.            *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    KEY,             \* set of keys in the store
    CLIENT,          \* set of transaction clients
    CLIENT_KEY,      \* [CLIENT -> SUBSET KEY] : keys written by each client
    CLIENT_PRIMARY   \* [CLIENT -> KEY]        : primary key of each client

ASSUME \A c \in CLIENT :
          /\ CLIENT_KEY[c] \subseteq KEY
          /\ CLIENT_KEY[c] # {}
          /\ CLIENT_PRIMARY[c] \in CLIENT_KEY[c]

VARIABLES
    next_ts,           \* timestamp oracle: next timestamp to hand out
    client_state,      \* lifecycle state of each client
    client_ts,         \* [start_ts, commit_ts] of each client
    client_read,       \* snapshot reads: version (writer's start_ts) read per key
    key_lock,          \* set of locks on each key
    key_write,         \* set of write/rollback records on each key
    key_last_read_ts   \* max read timestamp seen per key (max_ts)

vars == << next_ts, client_state, client_ts, client_read,
           key_lock, key_write, key_last_read_ts >>

NoRead == -1

States == {"init", "working", "prewriting", "committing", "committed", "aborted"}

Max(S) == CHOOSE x \in S : \A y \in S : y <= x
Max2(a, b) == IF a >= b THEN a ELSE b

Ts(c) == client_ts[c].start_ts

OwnLock(c, k) == {l \in key_lock[k] : l.start_ts = Ts(c)}

AllLocked(c) == \A k \in CLIENT_KEY[c] : OwnLock(c, k) # {}

\* Start timestamp of the latest committed version of k visible at ts.
LatestVersion(k, ts) ==
    LET vis    == {w \in key_write[k] : w.type = "write" /\ w.commit_ts <= ts}
        latest == CHOOSE w \in vis : \A w2 \in vis : w2.commit_ts <= w.commit_ts
    IN  latest.start_ts

\* Symmetry: clients that share the same primary and key set are
\* interchangeable. Use this as the SYMMETRY set in TLC.
ClientSymmetry ==
    UNION { Permutations({c \in CLIENT :
                              /\ CLIENT_PRIMARY[c] = CLIENT_PRIMARY[d]
                              /\ CLIENT_KEY[c] = CLIENT_KEY[d]}) : d \in CLIENT }

-----------------------------------------------------------------------------
Init ==
    /\ next_ts = 1
    /\ client_state = [c \in CLIENT |-> "init"]
    /\ client_ts = [c \in CLIENT |-> [start_ts |-> 0, commit_ts |-> 0]]
    /\ client_read = [c \in CLIENT |-> [k \in KEY |-> NoRead]]
    /\ key_lock = [k \in KEY |-> {}]
    \* The initial version of every key is written at timestamp 0.
    /\ key_write = [k \in KEY |->
                      {[type |-> "write", start_ts |-> 0, commit_ts |-> 0]}]
    /\ key_last_read_ts = [k \in KEY |-> 0]

\* Get a start timestamp from the oracle.
Start(c) ==
    /\ client_state[c] = "init"
    /\ client_state' = [client_state EXCEPT ![c] = "working"]
    /\ client_ts' = [client_ts EXCEPT ![c].start_ts = next_ts]
    /\ next_ts' = next_ts + 1
    /\ UNCHANGED << client_read, key_lock, key_write, key_last_read_ts >>

\* Snapshot read at start_ts. The read records max_ts. A read is blocked by
\* a foreign lock whose min_commit_ts could still be <= the read timestamp.
Read(c, k) ==
    /\ client_state[c] = "working"
    /\ client_read[c][k] = NoRead
    /\ ~\E l \in key_lock[k] : l.start_ts # Ts(c) /\ l.min_commit_ts <= Ts(c)
    /\ key_last_read_ts' = [key_last_read_ts EXCEPT ![k] = Max2(@, Ts(c))]
    /\ client_read' = [client_read EXCEPT ![c][k] = LatestVersion(k, Ts(c))]
    /\ UNCHANGED << next_ts, client_state, client_ts, key_lock, key_write >>

BeginPrewrite(c) ==
    /\ client_state[c] = "working"
    /\ client_state' = [client_state EXCEPT ![c] = "prewriting"]
    /\ UNCHANGED << next_ts, client_ts, client_read, key_lock, key_write,
                    key_last_read_ts >>

\* Prewrite one key. It fails (is disabled) on a lock or on a newer write.
\* The lock records an optimized min_commit_ts.
Prewrite(c, k) ==
    /\ client_state[c] = "prewriting"
    /\ k \in CLIENT_KEY[c]
    /\ key_lock[k] = {}
    /\ ~\E w \in key_write[k] : w.type = "write" /\ w.commit_ts >= Ts(c)
    /\ ~\E w \in key_write[k] : w.type = "rollback" /\ w.start_ts = Ts(c)
    /\ key_lock' = [key_lock EXCEPT ![k] =
                      {[start_ts      |-> Ts(c),
                        primary       |-> CLIENT_PRIMARY[c],
                        min_commit_ts |-> Max2(Ts(c), key_last_read_ts[k]) + 1]}]
    /\ UNCHANGED << next_ts, client_state, client_ts, client_read, key_write,
                    key_last_read_ts >>

\* All keys are prewritten, so the transaction is decided. The commit_ts is
\* computed from the locks' min_commit_ts without contacting the oracle.
\* The commit record goes to the primary key first.
CommitPrimary(c) ==
    /\ client_state[c] = "prewriting"
    /\ AllLocked(c)
    /\ LET locks == UNION {OwnLock(c, k) : k \in CLIENT_KEY[c]}
           cts   == Max({l.min_commit_ts : l \in locks})
           p     == CLIENT_PRIMARY[c]
       IN  /\ client_ts' = [client_ts EXCEPT ![c].commit_ts = cts]
           /\ key_lock' = [key_lock EXCEPT ![p] = @ \ OwnLock(c, p)]
           /\ key_write' = [key_write EXCEPT ![p] = @ \cup
                              {[type |-> "write", start_ts |-> Ts(c),
                                commit_ts |-> cts]}]
    /\ client_state' = [client_state EXCEPT ![c] = "committing"]
    /\ UNCHANGED << next_ts, client_read, key_last_read_ts >>

CommitSecondary(c, k) ==
    /\ client_state[c] = "committing"
    /\ k \in CLIENT_KEY[c] \ {CLIENT_PRIMARY[c]}
    /\ OwnLock(c, k) # {}
    /\ key_lock' = [key_lock EXCEPT ![k] = @ \ OwnLock(c, k)]
    /\ key_write' = [key_write EXCEPT ![k] = @ \cup
                       {[type |-> "write", start_ts |-> Ts(c),
                         commit_ts |-> client_ts[c].commit_ts]}]
    /\ UNCHANGED << next_ts, client_state, client_ts, client_read,
                    key_last_read_ts >>

FinishCommit(c) ==
    /\ client_state[c] = "committing"
    /\ \A k \in CLIENT_KEY[c] : OwnLock(c, k) = {}
    /\ client_state' = [client_state EXCEPT ![c] = "committed"]
    /\ UNCHANGED << next_ts, client_ts, client_read, key_lock, key_write,
                    key_last_read_ts >>

\* Abort is only possible before every key is locked. Once all keys are
\* locked the transaction is logically committed.
Abort(c) ==
    /\ client_state[c] \in {"working", "prewriting"}
    /\ ~AllLocked(c)
    /\ key_lock' = [k \in KEY |-> key_lock[k] \ OwnLock(c, k)]
    /\ key_write' = [k \in KEY |->
                       IF k \in CLIENT_KEY[c]
                       THEN key_write[k] \cup
                              {[type |-> "rollback", start_ts |-> Ts(c),
                                commit_ts |-> Ts(c)]}
                       ELSE key_write[k]]
    /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
    /\ UNCHANGED << next_ts, client_ts, client_read, key_last_read_ts >>

Next ==
    \E c \in CLIENT :
        \/ Start(c)
        \/ \E k \in KEY : Read(c, k)
        \/ BeginPrewrite(c)
        \/ \E k \in KEY : Prewrite(c, k)
        \/ CommitPrimary(c)
        \/ \E k \in KEY : CommitSecondary(c, k)
        \/ FinishCommit(c)
        \/ Abort(c)

Fairness ==
    \A c \in CLIENT :
        /\ WF_vars(Start(c))
        /\ WF_vars(BeginPrewrite(c))
        /\ \A k \in KEY : WF_vars(Prewrite(c, k))
        /\ WF_vars(CommitPrimary(c))
        /\ \A k \in KEY : WF_vars(CommitSecondary(c, k))
        /\ WF_vars(FinishCommit(c))
        /\ WF_vars(Abort(c))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK ==
    /\ next_ts \in Nat \ {0}
    /\ client_state \in [CLIENT -> States]
    /\ client_ts \in [CLIENT -> [start_ts : Nat, commit_ts : Nat]]
    /\ client_read \in [CLIENT -> [KEY -> Nat \cup {NoRead}]]
    /\ key_last_read_ts \in [KEY -> Nat]
    /\ \A k \in KEY :
         /\ Cardinality(key_lock[k]) <= 1
         /\ \A l \in key_lock[k] :
              l.start_ts \in Nat /\ l.primary \in KEY /\ l.min_commit_ts \in Nat
         /\ \A w \in key_write[k] :
              w.type \in {"write", "rollback"}
              /\ w.start_ts \in Nat /\ w.commit_ts \in Nat

\* Snapshot isolation (read side): every read returned exactly the latest
\* version committed at or before the reader's start_ts. This holds now and
\* in every later state, so no commit ever lands "in the past" of a read.
ReadConsistency ==
    \A c \in CLIENT : \A k \in KEY :
        client_read[c][k] # NoRead =>
            client_read[c][k] = LatestVersion(k, Ts(c))

\* No lost updates: committed writes to the same key never overlap in their
\* [start_ts, commit_ts] intervals, so they are totally ordered.
NoLostUpdate ==
    \A k \in KEY : \A w1, w2 \in key_write[k] :
        (w1.type = "write" /\ w2.type = "write" /\ w1 # w2) =>
            (w1.commit_ts < w2.start_ts \/ w2.commit_ts < w1.start_ts)

\* Timestamp consistency: commit_ts follows start_ts, and it never exceeds
\* the oracle. Any transaction that starts after a commit therefore has
\* start_ts >= commit_ts and observes it.
TimestampConsistency ==
    \A c \in CLIENT :
        client_state[c] \in {"committing", "committed"} =>
            /\ Ts(c) < client_ts[c].commit_ts
            /\ client_ts[c].commit_ts <= next_ts

\* Optimization invariant: every lock's min_commit_ts exceeds every read
\* timestamp already served on that key.
MinCommitTsSafe ==
    \A k \in KEY : \A l \in key_lock[k] : l.min_commit_ts > key_last_read_ts[k]

\* Atomicity: a committed transaction has all keys committed (or still
\* locked and pending) with one commit_ts and no rollbacks. An aborted
\* transaction has no committed writes and no locks.
Atomicity ==
    \A c \in CLIENT :
        /\ client_state[c] \in {"committing", "committed"} =>
             \A k \in CLIENT_KEY[c] :
                /\ \/ OwnLock(c, k) # {}
                   \/ \E w \in key_write[k] :
                        w.type = "write" /\ w.start_ts = Ts(c)
                        /\ w.commit_ts = client_ts[c].commit_ts
                /\ ~\E w \in key_write[k] :
                        w.type = "rollback" /\ w.start_ts = Ts(c)
        /\ client_state[c] = "committed" =>
             \A k \in CLIENT_KEY[c] : OwnLock(c, k) = {}
        /\ client_state[c] = "aborted" =>
             \A k \in KEY :
                /\ OwnLock(c, k) = {}
                /\ ~\E w \in key_write[k] :
                        w.type = "write" /\ w.start_ts = Ts(c)

\* The primary is the decision point: if any key holds a commit record for a
\* transaction, then the primary holds it too.
PrimaryCoordination ==
    \A c \in CLIENT : \A k \in CLIENT_KEY[c] :
        (Ts(c) > 0 /\ \E w \in key_write[k] : w.type = "write" /\ w.start_ts = Ts(c))
            => \E w \in key_write[CLIENT_PRIMARY[c]] :
                  w.type = "write" /\ w.start_ts = Ts(c)

Invariants ==
    /\ TypeOK
    /\ ReadConsistency
    /\ NoLostUpdate
    /\ TimestampConsistency
    /\ MinCommitTsSafe
    /\ Atomicity
    /\ PrimaryCoordination

-----------------------------------------------------------------------------
(* Liveness properties *)

Termination ==
    <>(\A c \in CLIENT : client_state[c] \in {"committed", "aborted"})

LocksEventuallyReleased ==
    <>[](\A k \in KEY : key_lock[k] = {})

THEOREM Spec => []Invariants
THEOREM Spec => Termination /\ LocksEventuallyReleased
=============================================================================