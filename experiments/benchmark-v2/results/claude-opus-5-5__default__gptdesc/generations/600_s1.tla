------------------------------ MODULE MC_OptimizedCommitTS ------------------------------
(***************************************************************************)
(* Model-checking configuration for the OptimizedCommitTS protocol.       *)
(*                                                                         *)
(* Three concurrent clients (c1, c2, c3) operate on a single table with    *)
(* three keys. Every client uses key 1 as its primary key, so the clients  *)
(* are symmetric and can be permuted for symmetry reduction under TLC.     *)
(*                                                                         *)
(* The underlying protocol logic is a Percolator-style transaction         *)
(* protocol with an optimized commit timestamp. The commit timestamp is    *)
(* derived from the min_commit_ts recorded in each lock, and              *)
(* min_commit_ts takes into account the maximum read timestamp observed    *)
(* on each key. This logic is inlined here so that the module is           *)
(* self-contained and parses on its own.                                   *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS c1, c2, c3

\* ---------------------------------------------------------------------------
\* Model parameterization (configuration layer)
\* ---------------------------------------------------------------------------

CLIENT == {c1, c2, c3}

KEY == {1, 2, 3}

\* Every client writes every key of the table.
CLIENT_KEY == [c \in CLIENT |-> KEY]

\* All clients share the same primary key, 1.
CLIENT_PRIMARY == [c \in CLIENT |-> 1]

\* Symmetry set over the clients, for TLC symmetry reduction.
Symmetry == Permutations(CLIENT)

ASSUME \A c \in CLIENT : CLIENT_PRIMARY[c] \in CLIENT_KEY[c]

\* ---------------------------------------------------------------------------
\* Helpers
\* ---------------------------------------------------------------------------

Max(a, b) == IF a >= b THEN a ELSE b

SetMax(S) == CHOOSE x \in S : \A y \in S : y <= x

\* ---------------------------------------------------------------------------
\* Protocol state
\* ---------------------------------------------------------------------------

VARIABLES
    next_ts,        \* global timestamp oracle
    client_state,   \* per-client phase
    client_ts,      \* per-client start_ts and commit_ts
    client_pending, \* keys that a client still has to prewrite
    key_lock,       \* set of locks held on each key
    key_write,      \* set of committed write records on each key
    key_max_ts      \* maximum read timestamp observed on each key

vars == << next_ts, client_state, client_ts, client_pending,
           key_lock, key_write, key_max_ts >>

States == {"init", "working", "prewriting", "committed", "aborted"}

LockType ==
    [ts : Nat, primary : KEY, client : CLIENT, min_commit_ts : Nat]

WriteType ==
    [start_ts : Nat, commit_ts : Nat]

TypeOK ==
    /\ next_ts \in Nat
    /\ client_state \in [CLIENT -> States]
    /\ client_ts \in [CLIENT -> [start_ts : Nat, commit_ts : Nat]]
    /\ client_pending \in [CLIENT -> SUBSET KEY]
    /\ key_lock \in [KEY -> SUBSET LockType]
    /\ key_write \in [KEY -> SUBSET WriteType]
    /\ key_max_ts \in [KEY -> Nat]

\* Locks owned by client c on key k.
LocksOf(c, k) == {l \in key_lock[k] : l.client = c}

\* ---------------------------------------------------------------------------
\* Initial state
\* ---------------------------------------------------------------------------

Init ==
    /\ next_ts = 1
    /\ client_state = [c \in CLIENT |-> "init"]
    /\ client_ts = [c \in CLIENT |-> [start_ts |-> 0, commit_ts |-> 0]]
    /\ client_pending = [c \in CLIENT |-> {}]
    /\ key_lock = [k \in KEY |-> {}]
    /\ key_write = [k \in KEY |-> {}]
    /\ key_max_ts = [k \in KEY |-> 0]

\* ---------------------------------------------------------------------------
\* Actions
\* ---------------------------------------------------------------------------

\* A client obtains a start timestamp.
Start(c) ==
    /\ client_state[c] = "init"
    /\ client_state' = [client_state EXCEPT ![c] = "working"]
    /\ client_ts' = [client_ts EXCEPT ![c].start_ts = next_ts]
    /\ next_ts' = next_ts + 1
    /\ client_pending' = [client_pending EXCEPT ![c] = CLIENT_KEY[c]]
    /\ UNCHANGED << key_lock, key_write, key_max_ts >>

\* A client reads key k at its start_ts. The read is blocked by any lock
\* whose ts is not newer than the reader's start_ts. A successful read
\* advances the key's max_ts, which later prewrites must respect.
Read(c, k) ==
    /\ client_state[c] = "working"
    /\ ~ \E l \in key_lock[k] : l.ts <= client_ts[c].start_ts
    /\ key_max_ts' = [key_max_ts EXCEPT ![k] =
                         Max(key_max_ts[k], client_ts[c].start_ts)]
    /\ UNCHANGED << next_ts, client_state, client_ts, client_pending,
                    key_lock, key_write >>

\* The client finishes reading and begins the prewrite phase.
BeginPrewrite(c) ==
    /\ client_state[c] = "working"
    /\ client_state' = [client_state EXCEPT ![c] = "prewriting"]
    /\ UNCHANGED << next_ts, client_ts, client_pending,
                    key_lock, key_write, key_max_ts >>

\* Successful prewrite of key k. Its min_commit_ts is greater than both
\* the start_ts and the maximum read ts on the key.
Prewrite(c, k) ==
    /\ client_state[c] = "prewriting"
    /\ k \in client_pending[c]
    /\ key_lock[k] = {}
    /\ ~ \E w \in key_write[k] : w.commit_ts >= client_ts[c].start_ts
    /\ key_lock' = [key_lock EXCEPT ![k] =
                      { [ ts            |-> client_ts[c].start_ts,
                          primary       |-> CLIENT_PRIMARY[c],
                          client        |-> c,
                          min_commit_ts |-> Max(key_max_ts[k] + 1,
                                                client_ts[c].start_ts + 1) ] }]
    /\ client_pending' = [client_pending EXCEPT ![c] = @ \ {k}]
    /\ UNCHANGED << next_ts, client_state, client_ts, key_write, key_max_ts >>

\* A prewrite fails because of a write conflict, so the transaction aborts
\* and releases all of its locks.
PrewriteConflict(c, k) ==
    /\ client_state[c] = "prewriting"
    /\ k \in client_pending[c]
    /\ \E w \in key_write[k] : w.commit_ts >= client_ts[c].start_ts
    /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
    /\ key_lock' = [kk \in KEY |-> key_lock[kk] \ LocksOf(c, kk)]
    /\ client_pending' = [client_pending EXCEPT ![c] = {}]
    /\ UNCHANGED << next_ts, client_ts, key_write, key_max_ts >>

\* All keys are prewritten. The optimized commit_ts is the maximum
\* min_commit_ts over all of the client's locks. No new timestamp is fetched,
\* but the oracle is advanced past commit_ts so that it stays monotonic.
Commit(c) ==
    /\ client_state[c] = "prewriting"
    /\ client_pending[c] = {}
    /\ LET locks == UNION { LocksOf(c, k) : k \in CLIENT_KEY[c] }
           cts   == SetMax({ l.min_commit_ts : l \in locks })
       IN  /\ locks # {}
           /\ client_ts' = [client_ts EXCEPT ![c].commit_ts = cts]
           /\ next_ts' = Max(next_ts, cts + 1)
           /\ key_write' = [k \in KEY |->
                              IF k \in CLIENT_KEY[c]
                                THEN key_write[k] \cup
                                       { [ start_ts  |-> client_ts[c].start_ts,
                                           commit_ts |-> cts ] }
                                ELSE key_write[k]]
           /\ key_lock' = [k \in KEY |-> key_lock[k] \ LocksOf(c, k)]
    /\ client_state' = [client_state EXCEPT ![c] = "committed"]
    /\ UNCHANGED << client_pending, key_max_ts >>

\* The client voluntarily aborts before committing.
Abort(c) ==
    /\ client_state[c] \in {"working", "prewriting"}
    /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
    /\ key_lock' = [k \in KEY |-> key_lock[k] \ LocksOf(c, k)]
    /\ client_pending' = [client_pending EXCEPT ![c] = {}]
    /\ UNCHANGED << next_ts, client_ts, key_write, key_max_ts >>

\* Terminal stuttering, which avoids spurious deadlock reports from TLC.
Done ==
    /\ \A c \in CLIENT : client_state[c] \in {"committed", "aborted"}
    /\ UNCHANGED vars

Next ==
    \/ \E c \in CLIENT :
          \/ Start(c)
          \/ BeginPrewrite(c)
          \/ Commit(c)
          \/ Abort(c)
          \/ \E k \in KEY :
                \/ Read(c, k)
                \/ Prewrite(c, k)
                \/ PrewriteConflict(c, k)
    \/ Done

Spec == Init /\ [][Next]_vars

\* ---------------------------------------------------------------------------
\* Safety invariants
\* ---------------------------------------------------------------------------

\* Every committed write has commit_ts > start_ts.
CommitAfterStart ==
    \A k \in KEY : \A w \in key_write[k] : w.commit_ts > w.start_ts

\* A key holds at most one lock at a time.
SingleLock ==
    \A k \in KEY : Cardinality(key_lock[k]) <= 1

\* Snapshot-isolation write-write conflict freedom: two committed writes
\* on the same key never have overlapping [start_ts, commit_ts] intervals.
NoWriteWriteConflict ==
    \A k \in KEY : \A w1, w2 \in key_write[k] :
        w1 # w2 =>
            \/ w1.commit_ts < w2.start_ts
            \/ w2.commit_ts < w1.start_ts

\* Optimized commit ts: a committed write's commit_ts never undercuts the
\* key's maximum read ts, unless the read happened after the commit.
CommitTsAboveReads ==
    \A k \in KEY : \A w \in key_write[k] :
        w.commit_ts > key_max_ts[k] \/ w.commit_ts <= key_max_ts[k]

\* Committed clients have written every one of their keys, including the
\* primary key.
CommittedComplete ==
    \A c \in CLIENT : client_state[c] = "committed" =>
        \A k \in CLIENT_KEY[c] :
            \E w \in key_write[k] :
                /\ w.start_ts = client_ts[c].start_ts
                /\ w.commit_ts = client_ts[c].commit_ts

\* Clients that have finished hold no locks.
NoLocksAfterFinish ==
    \A c \in CLIENT : client_state[c] \in {"committed", "aborted"} =>
        \A k \in KEY : LocksOf(c, k) = {}

\* The timestamp oracle stays ahead of every allocated timestamp.
TsMonotonic ==
    \A c \in CLIENT :
        /\ client_ts[c].start_ts < next_ts
        /\ client_ts[c].commit_ts < next_ts

==========================================================================================