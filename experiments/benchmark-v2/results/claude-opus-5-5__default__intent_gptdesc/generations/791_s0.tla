------------------------------ MODULE MVCCReplicatedKV ------------------------------
(***************************************************************************)
(* A replicated multi-version key-value store with transactions.           *)
(*                                                                         *)
(* Each transaction goes through three phases:                             *)
(*   1. Begin: it takes a snapshot timestamp equal to the current logical  *)
(*      commit clock.                                                      *)
(*   2. It reads and writes keys against that snapshot. Writes are         *)
(*      buffered privately. Reads of keys the transaction wrote itself     *)
(*      return the buffered value, which gives program order.              *)
(*   3. TryCommit: it validates using backward optimistic concurrency      *)
(*      control. If no key it read or wrote was overwritten after its      *)
(*      snapshot, all of its writes are installed in one atomic step with  *)
(*      a single fresh commit timestamp. Otherwise it aborts.              *)
(*                                                                         *)
(* Replicas expose versions by timestamp. A reader with snapshot s sees,   *)
(* for each key, the newest version whose timestamp is at most s.         *)
(* Because commits install every write with one timestamp in one step,     *)
(* visibility is all-or-nothing. Because the snapshot is taken from the   *)
(* global commit clock, it respects real time and causality.              *)
(*                                                                         *)
(* The serial order is the commit order recorded in `log`. Validation      *)
(* makes each committed transaction equivalent to running alone at its     *)
(* commit point.                                                           *)
(*                                                                         *)
(* An aborted transaction may restart and retry.                           *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    Keys,     \* set of keys
    Txns,     \* set of transaction (client) identifiers
    Values,   \* set of writable values
    NoVal,    \* marker for "no buffered write"
    NoTxn     \* writer of the initial versions

ASSUME /\ Keys # {}
       /\ Txns # {}
       /\ Values # {}
       /\ NoVal \notin Values
       /\ NoTxn \notin Txns

InitVal == CHOOSE v \in Values : TRUE

VARIABLES
    clock,      \* logical commit clock = last assigned commit timestamp
    store,      \* store[k] : sequence of versions [val, ts, writer]
    status,     \* status[t] \in {"idle","active","committed","aborted"}
    snapshot,   \* snapshot[t] : snapshot timestamp of t
    commitTs,   \* commitTs[t] : commit identifier of t (0 = none)
    readVer,    \* readVer[t][k] : ts of the version t read from the store (-1 = none)
    readVal,    \* readVal[t][k] : value t observed from the store
    writes,     \* writes[t][k] : buffered write of t (NoVal = none)
    log         \* serial commit order

vars == <<clock, store, status, snapshot, commitTs, readVer, readVal, writes, log>>

Status == {"idle", "active", "committed", "aborted"}

Version == [val : Values, ts : Nat, writer : Txns \cup {NoTxn}]

-----------------------------------------------------------------------------
(* Helper operators *)

Idx(k) == 1..Len(store[k])

LatestTs(k) == store[k][Len(store[k])].ts

\* The newest version of k with timestamp <= ts.
\* It is well defined for ts >= 0 because the initial version has ts 0.
VisibleVer(k, ts) ==
    LET i == CHOOSE i \in Idx(k) :
                /\ store[k][i].ts <= ts
                /\ \A j \in Idx(k) : store[k][j].ts <= ts => j <= i
    IN store[k][i]

ReadKeys(t)  == {k \in Keys : readVer[t][k] # -1}
WriteKeys(t) == {k \in Keys : writes[t][k] # NoVal}

\* Backward validation that resolves conflicts. The first committer wins
\* on write-write conflicts. A transaction also aborts if anything it read
\* changed after its snapshot.
Valid(t) == \A k \in ReadKeys(t) \cup WriteKeys(t) : LatestTs(k) <= snapshot[t]

Committed == {t \in Txns : status[t] = "committed"}

-----------------------------------------------------------------------------
TypeOK ==
    /\ clock \in Nat
    /\ store \in [Keys -> Seq(Version)]
    /\ \A k \in Keys : Len(store[k]) >= 1
    /\ status \in [Txns -> Status]
    /\ snapshot \in [Txns -> Nat]
    /\ commitTs \in [Txns -> Nat]
    /\ readVer \in [Txns -> [Keys -> Nat \cup {-1}]]
    /\ readVal \in [Txns -> [Keys -> Values \cup {NoVal}]]
    /\ writes \in [Txns -> [Keys -> Values \cup {NoVal}]]
    /\ log \in Seq(Txns)

-----------------------------------------------------------------------------
Init ==
    /\ clock = 0
    /\ store = [k \in Keys |-> << [val |-> InitVal, ts |-> 0, writer |-> NoTxn] >>]
    /\ status = [t \in Txns |-> "idle"]
    /\ snapshot = [t \in Txns |-> 0]
    /\ commitTs = [t \in Txns |-> 0]
    /\ readVer = [t \in Txns |-> [k \in Keys |-> -1]]
    /\ readVal = [t \in Txns |-> [k \in Keys |-> NoVal]]
    /\ writes = [t \in Txns |-> [k \in Keys |-> NoVal]]
    /\ log = << >>

\* Phase 1: acquire a snapshot.
Begin(t) ==
    /\ status[t] = "idle"
    /\ status' = [status EXCEPT ![t] = "active"]
    /\ snapshot' = [snapshot EXCEPT ![t] = clock]
    /\ UNCHANGED <<clock, store, commitTs, readVer, readVal, writes, log>>

\* Phase 2: a snapshot read.
\* It applies only to keys the transaction has not yet read or written.
\* Repeated reads return the recorded value. Reads of own writes return
\* the buffered value.
Read(t, k) ==
    /\ status[t] = "active"
    /\ writes[t][k] = NoVal
    /\ readVer[t][k] = -1
    /\ LET v == VisibleVer(k, snapshot[t]) IN
         /\ readVer' = [readVer EXCEPT ![t][k] = v.ts]
         /\ readVal' = [readVal EXCEPT ![t][k] = v.val]
    /\ UNCHANGED <<clock, store, status, snapshot, commitTs, writes, log>>

\* Phase 2: a buffered write.
Write(t, k, v) ==
    /\ status[t] = "active"
    /\ writes' = [writes EXCEPT ![t][k] = v]
    /\ UNCHANGED <<clock, store, status, snapshot, commitTs, readVer, readVal, log>>

\* Phase 3: an atomic commit at a single logical commit point, or an abort
\* on conflict.
TryCommit(t) ==
    /\ status[t] = "active"
    /\ IF Valid(t)
       THEN LET c == clock + 1 IN
            /\ store' = [k \in Keys |->
                           IF writes[t][k] # NoVal
                           THEN Append(store[k],
                                       [val |-> writes[t][k], ts |-> c, writer |-> t])
                           ELSE store[k]]
            /\ clock' = c
            /\ commitTs' = [commitTs EXCEPT ![t] = c]
            /\ status' = [status EXCEPT ![t] = "committed"]
            /\ log' = Append(log, t)
       ELSE /\ status' = [status EXCEPT ![t] = "aborted"]
            /\ UNCHANGED <<store, clock, commitTs, log>>
    /\ UNCHANGED <<snapshot, readVer, readVal, writes>>

\* An aborted transaction discards its state and retries.
Restart(t) ==
    /\ status[t] = "aborted"
    /\ status' = [status EXCEPT ![t] = "idle"]
    /\ snapshot' = [snapshot EXCEPT ![t] = 0]
    /\ readVer' = [readVer EXCEPT ![t] = [k \in Keys |-> -1]]
    /\ readVal' = [readVal EXCEPT ![t] = [k \in Keys |-> NoVal]]
    /\ writes' = [writes EXCEPT ![t] = [k \in Keys |-> NoVal]]
    /\ UNCHANGED <<clock, store, commitTs, log>>

\* Terminal stuttering once every transaction has committed.
Done ==
    /\ \A t \in Txns : status[t] = "committed"
    /\ UNCHANGED vars

Next ==
    \/ \E t \in Txns :
         \/ Begin(t)
         \/ \E k \in Keys : Read(t, k)
         \/ \E k \in Keys, v \in Values : Write(t, k, v)
         \/ TryCommit(t)
         \/ Restart(t)
    \/ Done

\* Minimal fairness for nonfaulty clients. They eventually start, they
\* eventually try to commit, and they eventually retry after an abort.
\* Reads and writes need no fairness.
Fairness ==
    \A t \in Txns :
        /\ WF_vars(Begin(t))
        /\ WF_vars(TryCommit(t))
        /\ WF_vars(Restart(t))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

\* Version monotonicity: the versions of each key are ordered by strictly
\* increasing timestamps, and no version is newer than the clock.
VersionMonotonicity ==
    \A k \in Keys :
        /\ \A i, j \in Idx(k) : i < j => store[k][i].ts < store[k][j].ts
        /\ LatestTs(k) <= clock

\* Commit identifiers are unique. They also match the serial log order.
UniqueCommitIds ==
    /\ \A t, u \in Committed : t # u => commitTs[t] # commitTs[u]
    /\ \A t \in Committed : commitTs[t] \in 1..clock
    /\ \A t \in Txns \ Committed : commitTs[t] = 0
    /\ Len(log) = clock
    /\ \A i \in 1..Len(log) : status[log[i]] = "committed" /\ commitTs[log[i]] = i
    /\ \A i, j \in 1..Len(log) : i # j => log[i] # log[j]

\* Atomicity is all-or-nothing visibility:
\*  - every write of a committed transaction is present at its commit timestamp;
\*  - no write of an uncommitted transaction is present;
\*  - all versions sharing a timestamp come from one committed writer.
Atomicity ==
    /\ \A t \in Committed : \A k \in WriteKeys(t) :
          \E i \in Idx(k) : store[k][i] = [val |-> writes[t][k],
                                            ts |-> commitTs[t], writer |-> t]
    /\ \A k \in Keys : \A i \in Idx(k) :
          LET w == store[k][i].writer IN
          w # NoTxn =>
             /\ status[w] = "committed"
             /\ store[k][i].ts = commitTs[w]
             /\ k \in WriteKeys(w)
    /\ \A k1, k2 \in Keys : \A i \in Idx(k1), j \in Idx(k2) :
          store[k1][i].ts = store[k2][j].ts =>
             store[k1][i].writer = store[k2][j].writer

\* Snapshot isolation:
\*  - every store read of an active or committed transaction returns the
\*    version visible in its single snapshot;
\*  - first committer wins, so concurrent committed transactions never
\*    write the same key.
SnapshotIsolation ==
    /\ \A t \in Txns : status[t] \in {"active", "committed"} =>
          \A k \in ReadKeys(t) :
             LET v == VisibleVer(k, snapshot[t]) IN
             /\ readVer[t][k] = v.ts
             /\ readVal[t][k] = v.val
    /\ \A t, u \in Committed :
          (t # u /\ snapshot[t] < commitTs[u] /\ commitTs[u] < commitTs[t])
              => WriteKeys(t) \cap WriteKeys(u) = {}

\* Causal and real-time consistency of reads:
\*  - a snapshot never lies in the future;
\*  - a read only observes writes of transactions that committed at or
\*    before the snapshot;
\*  - all other writes of that writer are also visible in the snapshot.
CausalVisibility ==
    \A t \in Txns : status[t] \in {"active", "committed"} =>
       /\ snapshot[t] <= clock
       /\ \A k \in ReadKeys(t) :
            LET u == VisibleVer(k, snapshot[t]).writer IN
            u # NoTxn =>
               /\ status[u] = "committed"
               /\ commitTs[u] <= snapshot[t]
               /\ \A k2 \in WriteKeys(u) :
                     VisibleVer(k2, snapshot[t]).ts >= commitTs[u]

\* Serializability, which is also linearizable with respect to commits.
\* Every committed transaction behaves as if it ran alone at its commit
\* point in the serial order `log`. So each store read equals the latest
\* version committed before it. Its snapshot precedes its commit, and its
\* commit point lies within its real-time interval.
Serializability ==
    \A t \in Committed :
       /\ snapshot[t] < commitTs[t]
       /\ \A k \in ReadKeys(t) :
            LET v == VisibleVer(k, commitTs[t] - 1) IN
            /\ readVer[t][k] = v.ts
            /\ readVal[t][k] = v.val

Invariants ==
    /\ TypeOK
    /\ VersionMonotonicity
    /\ UniqueCommitIds
    /\ Atomicity
    /\ SnapshotIsolation
    /\ CausalVisibility
    /\ Serializability

\* Committed data is never lost or rewritten. It is only extended.
StoreGrowsOnly ==
    [][\A k \in Keys :
          /\ Len(store'[k]) >= Len(store[k])
          /\ SubSeq(store'[k], 1, Len(store[k])) = store[k]]_vars

\* Once committed, a transaction stays committed with the same identifier.
CommitStable ==
    [][\A t \in Txns : status[t] = "committed" =>
          (status'[t] = "committed" /\ commitTs'[t] = commitTs[t])]_vars

-----------------------------------------------------------------------------
(* Liveness properties *)

\* Every started transaction eventually commits or aborts. It never blocks.
EventualDecision ==
    \A t \in Txns : (status[t] = "active") ~> (status[t] \in {"committed", "aborted"})

\* Progress without indefinite contention. If other transactions eventually
\* stop committing, every nonfaulty client eventually commits.
NoStarvationWithoutContention ==
    \A t \in Txns :
       (<>[][\A u \in Txns \ {t} :
                ~(status[u] # "committed" /\ status'[u] = "committed")]_vars)
          => <>(status[t] = "committed")

\* With a finite set of transactions, every transaction eventually commits.
AllEventuallyCommit == <>(\A t \in Txns : status[t] = "committed")

THEOREM Spec => []Invariants
THEOREM Spec => StoreGrowsOnly /\ CommitStable
THEOREM Spec => EventualDecision /\ NoStarvationWithoutContention
=============================================================================