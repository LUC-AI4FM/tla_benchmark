------------------------- MODULE DistributedTransactionOptimizedTs -------------------------
(***************************************************************************)
(* A Percolator-style distributed transaction commit protocol with an      *)
(* "async commit" style timestamp optimisation.                            *)
(*                                                                         *)
(*  - Each client runs one transaction. It writes the keys CLIENT_KEY[c]   *)
(*    and coordinates through its primary key CLIENT_PRIMARY[c].          *)
(*  - Reads record the reader's start_ts in key_max_ts[k].                 *)
(*  - Each prewrite lock gets a min_commit_ts of                          *)
(*    Max(start_ts, key_max_ts[k]) + 1.                                    *)
(*  - The commit timestamp is not fetched from a timestamp oracle. It is   *)
(*    the maximum min_commit_ts over all of the transaction's locks.       *)
(*  - The commit is applied to the primary key first and then to the      *)
(*    secondary keys.                                                      *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS KEY,            \* set of keys in the store
          CLIENT,         \* set of clients
          CLIENT_KEY,     \* CLIENT_KEY[c] : keys written by client c
          CLIENT_PRIMARY  \* CLIENT_PRIMARY[c] : primary key of client c

ASSUME /\ KEY # {}
       /\ CLIENT # {}
       /\ CLIENT_KEY \in [CLIENT -> SUBSET KEY]
       /\ CLIENT_PRIMARY \in [CLIENT -> KEY]
       /\ \A c \in CLIENT : CLIENT_PRIMARY[c] \in CLIENT_KEY[c]
       /\ \A c1, c2 \in CLIENT : c1 # c2 => CLIENT_PRIMARY[c1] # CLIENT_PRIMARY[c2]

VARIABLES next_ts,        \* timestamp oracle
          client_state,   \* per-client protocol state
          client_ts,      \* [start_ts, commit_ts] per client
          client_read,    \* keys already read by each client
          key_lock,       \* key -> set of locks (at most one)
          key_data,       \* key -> set of start_ts of written (uncommitted/committed) data
          key_write,      \* key -> set of commit records [start_ts, commit_ts]
          key_max_ts,     \* key -> max start_ts of any reader of that key
          read_history    \* history of snapshot reads (for checking)

vars == << next_ts, client_state, client_ts, client_read, key_lock,
           key_data, key_write, key_max_ts, read_history >>

States == {"init", "working", "prewriting", "committing", "committed", "aborted"}

MaxOf(a, b) == IF a >= b THEN a ELSE b
MaxSet(S)   == CHOOSE x \in S : \A y \in S : y <= x

StartTs(c)  == client_ts[c].start_ts

\* Lock on k owned by transaction with start_ts ts
LocksBy(k, ts) == {l \in key_lock[k] : l.ts = ts}
HasLockBy(k, ts) == LocksBy(k, ts) # {}

\* Commit ts of the latest version of k visible at snapshot ts (0 = none)
LatestCommitBefore(k, ts) ==
    LET W == {w \in key_write[k] : w.commit_ts <= ts}
    IN IF W = {} THEN 0 ELSE MaxSet({w.commit_ts : w \in W})

LockRec == [ts : Nat, primary : KEY, min_commit_ts : Nat]
WriteRec == [start_ts : Nat, commit_ts : Nat]
ReadRec == [client : CLIENT, key : KEY, ts : Nat, val : Nat]

-----------------------------------------------------------------------------
Init ==
    /\ next_ts = 1
    /\ client_state = [c \in CLIENT |-> "init"]
    /\ client_ts = [c \in CLIENT |-> [start_ts |-> 0, commit_ts |-> 0]]
    /\ client_read = [c \in CLIENT |-> {}]
    /\ key_lock = [k \in KEY |-> {}]
    /\ key_data = [k \in KEY |-> {}]
    /\ key_write = [k \in KEY |-> {}]
    /\ key_max_ts = [k \in KEY |-> 0]
    /\ read_history = {}

\* Client obtains a start timestamp from the oracle
Start(c) ==
    /\ client_state[c] = "init"
    /\ client_state' = [client_state EXCEPT ![c] = "working"]
    /\ client_ts' = [client_ts EXCEPT ![c].start_ts = next_ts]
    /\ next_ts' = next_ts + 1
    /\ UNCHANGED << client_read, key_lock, key_data, key_write, key_max_ts, read_history >>

\* Snapshot read of key k at start_ts. It is blocked by any lock of an older
\* transaction. The read updates key_max_ts so that later commits get a
\* larger commit timestamp.
Read(c, k) ==
    /\ client_state[c] = "working"
    /\ k \notin client_read[c]
    /\ ~\E l \in key_lock[k] : l.ts <= StartTs(c)
    /\ client_read' = [client_read EXCEPT ![c] = @ \cup {k}]
    /\ key_max_ts' = [key_max_ts EXCEPT ![k] = MaxOf(@, StartTs(c))]
    /\ read_history' = read_history \cup
         {[client |-> c, key |-> k, ts |-> StartTs(c),
           val |-> LatestCommitBefore(k, StartTs(c))]}
    /\ UNCHANGED << next_ts, client_state, client_ts, key_lock, key_data, key_write >>

\* Prewrite key k. This places a lock that carries an optimised min_commit_ts.
Prewrite(c, k) ==
    LET st == StartTs(c) IN
    /\ client_state[c] \in {"working", "prewriting"}
    /\ k \in CLIENT_KEY[c]
    /\ key_lock[k] = {}
    /\ ~\E w \in key_write[k] : w.commit_ts >= st
    /\ st \notin key_data[k]
    /\ key_lock' = [key_lock EXCEPT ![k] =
                      {[ts |-> st, primary |-> CLIENT_PRIMARY[c],
                        min_commit_ts |-> MaxOf(st, key_max_ts[k]) + 1]}]
    /\ key_data' = [key_data EXCEPT ![k] = @ \cup {st}]
    /\ client_state' = [client_state EXCEPT ![c] = "prewriting"]
    /\ UNCHANGED << next_ts, client_ts, client_read, key_write, key_max_ts, read_history >>

\* All locks are in place. The commit ts is the maximum min_commit_ts over
\* the locks. The primary key is committed first.
CommitPrimary(c) ==
    LET st  == StartTs(c)
        p   == CLIENT_PRIMARY[c]
        cts == MaxSet({l.min_commit_ts : l \in UNION {LocksBy(k, st) : k \in CLIENT_KEY[c]}})
    IN
    /\ client_state[c] = "prewriting"
    /\ \A k \in CLIENT_KEY[c] : HasLockBy(k, st)
    /\ client_ts' = [client_ts EXCEPT ![c].commit_ts = cts]
    /\ next_ts' = MaxOf(next_ts, cts + 1)
    /\ key_lock' = [key_lock EXCEPT ![p] = {l \in @ : l.ts # st}]
    /\ key_write' = [key_write EXCEPT ![p] = @ \cup {[start_ts |-> st, commit_ts |-> cts]}]
    /\ client_state' = [client_state EXCEPT ![c] = "committing"]
    /\ UNCHANGED << client_read, key_data, key_max_ts, read_history >>

\* Commit a secondary key using the commit ts that was already determined
CommitSecondary(c, k) ==
    LET st == StartTs(c) IN
    /\ client_state[c] = "committing"
    /\ k \in CLIENT_KEY[c]
    /\ HasLockBy(k, st)
    /\ key_lock' = [key_lock EXCEPT ![k] = {l \in @ : l.ts # st}]
    /\ key_write' = [key_write EXCEPT ![k] =
                       @ \cup {[start_ts |-> st, commit_ts |-> client_ts[c].commit_ts]}]
    /\ UNCHANGED << next_ts, client_state, client_ts, client_read, key_data,
                    key_max_ts, read_history >>

FinishCommit(c) ==
    /\ client_state[c] = "committing"
    /\ \A k \in CLIENT_KEY[c] : ~HasLockBy(k, StartTs(c))
    /\ client_state' = [client_state EXCEPT ![c] = "committed"]
    /\ UNCHANGED << next_ts, client_ts, client_read, key_lock, key_data, key_write,
                    key_max_ts, read_history >>

\* Abort before the commit point. All locks and data of the transaction are
\* rolled back.
Abort(c) ==
    LET st == StartTs(c) IN
    /\ client_state[c] \in {"working", "prewriting"}
    /\ key_lock' = [k \in KEY |-> {l \in key_lock[k] : l.ts # st}]
    /\ key_data' = [k \in KEY |-> key_data[k] \ {st}]
    /\ client_state' = [client_state EXCEPT ![c] = "aborted"]
    /\ UNCHANGED << next_ts, client_ts, client_read, key_write, key_max_ts, read_history >>

ClientAction(c) ==
    \/ Start(c)
    \/ \E k \in KEY : Read(c, k)
    \/ \E k \in KEY : Prewrite(c, k)
    \/ CommitPrimary(c)
    \/ \E k \in KEY : CommitSecondary(c, k)
    \/ FinishCommit(c)
    \/ Abort(c)

AllDone == \A c \in CLIENT : client_state[c] \in {"committed", "aborted"}

Terminating == AllDone /\ UNCHANGED vars

Next == (\E c \in CLIENT : ClientAction(c)) \/ Terminating

Fairness == \A c \in CLIENT : WF_vars(ClientAction(c))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK ==
    /\ next_ts \in Nat
    /\ client_state \in [CLIENT -> States]
    /\ client_ts \in [CLIENT -> [start_ts : Nat, commit_ts : Nat]]
    /\ client_read \in [CLIENT -> SUBSET KEY]
    /\ \A k \in KEY : key_lock[k] \subseteq LockRec /\ Cardinality(key_lock[k]) <= 1
    /\ key_data \in [KEY -> SUBSET Nat]
    /\ \A k \in KEY : key_write[k] \subseteq WriteRec
    /\ key_max_ts \in [KEY -> Nat]
    /\ read_history \subseteq ReadRec

\* Transaction isolation (snapshot isolation):
\* (1) Reads are stable. Every recorded snapshot read still sees the same
\*     latest version. Later commits can never land at or below a timestamp
\*     at which the key was already read.
\* (2) No two committed writes on the same key have overlapping
\*     [start_ts, commit_ts] intervals (first committer wins).
SnapshotReadStable ==
    \A r \in read_history : LatestCommitBefore(r.key, r.ts) = r.val

WriteWriteIsolation ==
    \A k \in KEY : \A w1, w2 \in key_write[k] :
        w1 # w2 => (w1.commit_ts < w2.start_ts \/ w2.commit_ts < w1.start_ts)

TransactionIsolation == SnapshotReadStable /\ WriteWriteIsolation

\* Commit consistency: every key that a transaction commits uses the same
\* commit timestamp.
CommitConsistency ==
    \A c \in CLIENT : \A k \in KEY : \A w \in key_write[k] :
        w.start_ts = StartTs(c) =>
            /\ client_state[c] \in {"committing", "committed"}
            /\ w.commit_ts = client_ts[c].commit_ts

\* Atomicity: a transaction either commits fully or aborts fully.
Atomicity ==
    \A c \in CLIENT :
        /\ client_state[c] = "aborted" =>
             \A k \in KEY :
                /\ ~\E w \in key_write[k] : w.start_ts = StartTs(c)
                /\ ~HasLockBy(k, StartTs(c))
                /\ StartTs(c) \notin key_data[k]
        /\ client_state[c] = "committed" =>
             \A k \in CLIENT_KEY[c] :
                /\ \E w \in key_write[k] : w.start_ts = StartTs(c)
                /\ ~HasLockBy(k, StartTs(c))
        /\ client_state[c] = "committing" =>
             \A k \in CLIENT_KEY[c] :
                (\E w \in key_write[k] : w.start_ts = StartTs(c)) \/ HasLockBy(k, StartTs(c))

\* Timestamp ordering: the optimised commit ts is larger than the start ts.
\* It is at least every lock's min_commit_ts, and it is below the oracle.
\* Locks always carry a min_commit_ts above every recorded read ts.
TimestampOrdering ==
    /\ \A c \in CLIENT :
         client_state[c] \in {"committing", "committed"} =>
            /\ client_ts[c].commit_ts > StartTs(c)
            /\ client_ts[c].commit_ts < next_ts
            /\ \A k \in CLIENT_KEY[c] : \A l \in LocksBy(k, StartTs(c)) :
                  l.min_commit_ts <= client_ts[c].commit_ts
    /\ \A c \in CLIENT : client_state[c] # "init" => StartTs(c) < next_ts
    /\ \A k \in KEY : \A l \in key_lock[k] :
         /\ l.min_commit_ts > l.ts
         /\ \A r \in read_history : r.key = k => l.min_commit_ts > r.ts
    /\ \A k \in KEY : \A w \in key_write[k] : w.commit_ts > w.start_ts

(* Liveness properties *)

AllTransactionsTerminate == <>AllDone

CommittingEventuallyCommitted ==
    \A c \in CLIENT : (client_state[c] = "committing") ~> (client_state[c] = "committed")

PrimaryCommitImpliesFullCommit ==
    \A c \in CLIENT :
        (\E w \in key_write[CLIENT_PRIMARY[c]] : w.start_ts = StartTs(c) /\ StartTs(c) > 0)
            ~> (client_state[c] = "committed")

=============================================================================