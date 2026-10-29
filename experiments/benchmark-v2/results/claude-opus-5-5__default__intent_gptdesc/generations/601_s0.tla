------------------------------ MODULE OptimisticTxnKV ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    Keys,       \* the keys of the single table
    Txns,       \* transaction identifiers (one per client transaction)
    Values,     \* values that may be written
    InitVal,    \* initial value of every key
    NoTxn,      \* sentinel: no lock holder / initial-version writer
    NoVal       \* sentinel: value not yet read

ASSUME InitVal \in Values
ASSUME NoTxn \notin Txns
ASSUME NoVal \notin Values

VARIABLES
    clock,      \* timestamp oracle; strictly increasing
    status,     \* status[t] \in {"idle","active","preparing","committed","aborted"}
    startTs,    \* snapshot (start) timestamp of t
    commitTs,   \* commit timestamp of t (0 if none)
    rs,         \* read set of t
    ws,         \* write set of t (non-empty)
    wval,       \* wval[t][k]: value t writes to k (meaningful for k \in ws[t])
    primary,    \* designated primary key of t (an element of ws[t])
    readDone,   \* keys t has already read
    readVal,    \* readVal[t][k]: value t observed for k
    prepared,   \* keys of ws[t] on which t holds a prepare lock
    applied,    \* keys of ws[t] on which t's version has been installed
    locks,      \* locks[k]: transaction holding the prepare lock on k, or NoTxn
    store,      \* store[k]: set of versions [ts, val, txn]
    up          \* up[k]: TRUE iff the owner of key k is not failed

vars == << clock, status, startTs, commitTs, rs, ws, wval, primary,
           readDone, readVal, prepared, applied, locks, store, up >>

Status == {"idle", "active", "preparing", "committed", "aborted"}
Version == [ts : Nat, val : Values, txn : Txns \cup {NoTxn}]

-----------------------------------------------------------------------------
(* Helpers *)

LatestTs(k) ==
    CHOOSE n \in {v.ts : v \in store[k]} : \A w \in store[k] : w.ts <= n

\* Latest version of k with timestamp <= ts (snapshot read)
VisibleAt(k, ts) ==
    CHOOSE v \in store[k] :
        /\ v.ts <= ts
        /\ \A w \in store[k] : w.ts <= ts => w.ts <= v.ts

LatestVersion(k) == VisibleAt(k, LatestTs(k))

ReleaseLocks(t) == [k \in Keys |-> IF locks[k] = t THEN NoTxn ELSE locks[k]]

\* Committed writers of k with commit timestamp strictly below ts
WritersBefore(k, ts) ==
    {u \in Txns : status[u] = "committed" /\ k \in ws[u] /\ commitTs[u] < ts}

\* Value of k in the serial execution ordered by commit timestamps,
\* considering only transactions with commit timestamp < ts
SerialVal(k, ts) ==
    LET W == WritersBefore(k, ts)
    IN IF W = {} THEN InitVal
       ELSE wval[CHOOSE u \in W : \A x \in W : commitTs[x] <= commitTs[u]][k]

-----------------------------------------------------------------------------
TypeOK ==
    /\ clock \in Nat
    /\ status \in [Txns -> Status]
    /\ startTs \in [Txns -> Nat]
    /\ commitTs \in [Txns -> Nat]
    /\ rs \in [Txns -> SUBSET Keys]
    /\ ws \in [Txns -> SUBSET Keys]
    /\ wval \in [Txns -> [Keys -> Values]]
    /\ primary \in [Txns -> Keys]
    /\ readDone \in [Txns -> SUBSET Keys]
    /\ readVal \in [Txns -> [Keys -> Values \cup {NoVal}]]
    /\ prepared \in [Txns -> SUBSET Keys]
    /\ applied \in [Txns -> SUBSET Keys]
    /\ locks \in [Keys -> Txns \cup {NoTxn}]
    /\ store \in [Keys -> SUBSET Version]
    /\ up \in [Keys -> BOOLEAN]

Init ==
    /\ clock = 0
    /\ status = [t \in Txns |-> "idle"]
    /\ startTs = [t \in Txns |-> 0]
    /\ commitTs = [t \in Txns |-> 0]
    /\ rs = [t \in Txns |-> {}]
    /\ ws = [t \in Txns |-> {}]
    /\ wval = [t \in Txns |-> [k \in Keys |-> InitVal]]
    /\ primary = [t \in Txns |-> CHOOSE k \in Keys : TRUE]
    /\ readDone = [t \in Txns |-> {}]
    /\ readVal = [t \in Txns |-> [k \in Keys |-> NoVal]]
    /\ prepared = [t \in Txns |-> {}]
    /\ applied = [t \in Txns |-> {}]
    /\ locks = [k \in Keys |-> NoTxn]
    /\ store = [k \in Keys |-> {[ts |-> 0, val |-> InitVal, txn |-> NoTxn]}]
    /\ up = [k \in Keys |-> TRUE]

-----------------------------------------------------------------------------
(* Actions *)

\* Client starts a transaction: picks read/write sets, primary, values,
\* and obtains a start timestamp from the oracle.
Begin(t) ==
    /\ status[t] = "idle"
    /\ \E R \in SUBSET Keys, W \in (SUBSET Keys) \ {{}} :
        \E p \in W, f \in [Keys -> Values] :
            /\ rs' = [rs EXCEPT ![t] = R]
            /\ ws' = [ws EXCEPT ![t] = W]
            /\ primary' = [primary EXCEPT ![t] = p]
            /\ wval' = [wval EXCEPT ![t] = f]
    /\ clock' = clock + 1
    /\ startTs' = [startTs EXCEPT ![t] = clock + 1]
    /\ status' = [status EXCEPT ![t] = "active"]
    /\ UNCHANGED << commitTs, readDone, readVal, prepared, applied, locks, store, up >>

\* Snapshot read at startTs; blocks while k is locked (a commit with a
\* smaller timestamp may not yet be installed).
Read(t, k) ==
    /\ status[t] = "active"
    /\ k \in rs[t] \ readDone[t]
    /\ locks[k] = NoTxn
    /\ readVal' = [readVal EXCEPT ![t][k] = VisibleAt(k, startTs[t]).val]
    /\ readDone' = [readDone EXCEPT ![t] = @ \cup {k}]
    /\ UNCHANGED << clock, status, startTs, commitTs, rs, ws, wval, primary,
                    prepared, applied, locks, store, up >>

\* Client proposes commit after all reads are done.
StartCommit(t) ==
    /\ status[t] = "active"
    /\ readDone[t] = rs[t]
    /\ status' = [status EXCEPT ![t] = "preparing"]
    /\ UNCHANGED << clock, startTs, commitTs, rs, ws, wval, primary, readDone,
                    readVal, prepared, applied, locks, store, up >>

\* A participant (primary or secondary) prepares: acquires the prepare lock
\* if there is no write-write conflict; otherwise the transaction aborts.
Prepare(t, k) ==
    /\ status[t] = "preparing"
    /\ k \in ws[t] \ prepared[t]
    /\ IF locks[k] = NoTxn /\ LatestTs(k) <= startTs[t]
       THEN /\ locks' = [locks EXCEPT ![k] = t]
            /\ prepared' = [prepared EXCEPT ![t] = @ \cup {k}]
            /\ UNCHANGED status
       ELSE /\ locks' = ReleaseLocks(t)
            /\ status' = [status EXCEPT ![t] = "aborted"]
            /\ UNCHANGED prepared
    /\ UNCHANGED << clock, startTs, commitTs, rs, ws, wval, primary, readDone,
                    readVal, applied, store, up >>

ReadSetValid(t) ==
    \A r \in rs[t] : LatestTs(r) <= startTs[t] /\ locks[r] \in {NoTxn, t}

\* Primary owner validates the read set and assigns the commit timestamp,
\* atomically making the commit decision and installing the primary write.
CommitPrimary(t) ==
    /\ status[t] = "preparing"
    /\ prepared[t] = ws[t]
    /\ up[primary[t]]
    /\ ReadSetValid(t)
    /\ clock' = clock + 1
    /\ commitTs' = [commitTs EXCEPT ![t] = clock + 1]
    /\ status' = [status EXCEPT ![t] = "committed"]
    /\ store' = [store EXCEPT ![primary[t]] =
                    @ \cup {[ts |-> clock + 1, val |-> wval[t][primary[t]], txn |-> t]}]
    /\ locks' = [locks EXCEPT ![primary[t]] = NoTxn]
    /\ applied' = [applied EXCEPT ![t] = {primary[t]}]
    /\ UNCHANGED << startTs, rs, ws, wval, primary, readDone, readVal, prepared, up >>

\* Primary owner detects read-set invalidation and aborts.
ValidationAbort(t) ==
    /\ status[t] = "preparing"
    /\ prepared[t] = ws[t]
    /\ up[primary[t]]
    /\ ~ReadSetValid(t)
    /\ status' = [status EXCEPT ![t] = "aborted"]
    /\ locks' = ReleaseLocks(t)
    /\ UNCHANGED << clock, startTs, commitTs, rs, ws, wval, primary, readDone,
                    readVal, prepared, applied, store, up >>

Decide(t) == CommitPrimary(t) \/ ValidationAbort(t)

\* A non-primary participant accepts the commit at the primary's timestamp.
AcceptSecondary(t, k) ==
    /\ status[t] = "committed"
    /\ k \in ws[t] \ applied[t]
    /\ store' = [store EXCEPT ![k] =
                    @ \cup {[ts |-> commitTs[t], val |-> wval[t][k], txn |-> t]}]
    /\ locks' = [locks EXCEPT ![k] = NoTxn]
    /\ applied' = [applied EXCEPT ![t] = @ \cup {k}]
    /\ UNCHANGED << clock, status, startTs, commitTs, rs, ws, wval, primary,
                    readDone, readVal, prepared, up >>

\* Voluntary client abort before a commit decision.
ClientAbort(t) ==
    /\ status[t] \in {"active", "preparing"}
    /\ status' = [status EXCEPT ![t] = "aborted"]
    /\ locks' = ReleaseLocks(t)
    /\ UNCHANGED << clock, startTs, commitTs, rs, ws, wval, primary, readDone,
                    readVal, prepared, applied, store, up >>

\* Transient failures of key owners (possibly a primary).
Fail(k) ==
    /\ up[k]
    /\ up' = [up EXCEPT ![k] = FALSE]
    /\ UNCHANGED << clock, status, startTs, commitTs, rs, ws, wval, primary,
                    readDone, readVal, prepared, applied, locks, store >>

Recover(k) ==
    /\ ~up[k]
    /\ up' = [up EXCEPT ![k] = TRUE]
    /\ UNCHANGED << clock, status, startTs, commitTs, rs, ws, wval, primary,
                    readDone, readVal, prepared, applied, locks, store >>

Terminated ==
    /\ \A t \in Txns : status[t] \in {"committed", "aborted"} /\
                       (status[t] = "committed" => applied[t] = ws[t])
    /\ UNCHANGED vars

Next ==
    \/ \E t \in Txns :
        \/ Begin(t)
        \/ StartCommit(t)
        \/ Decide(t)
        \/ ClientAbort(t)
        \/ \E k \in Keys : Read(t, k) \/ Prepare(t, k) \/ AcceptSecondary(t, k)
    \/ \E k \in Keys : Fail(k) \/ Recover(k)
    \/ Terminated

Fairness ==
    /\ \A t \in Txns :
        /\ WF_vars(StartCommit(t))
        /\ SF_vars(Decide(t))
        /\ \A k \in Keys :
            /\ SF_vars(Read(t, k))
            /\ WF_vars(Prepare(t, k))
            /\ WF_vars(AcceptSecondary(t, k))
    /\ \A k \in Keys : WF_vars(Recover(k))   \* no permanent failures

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

\* Timestamps are unique, comparable, and commit follows start.
TimestampsUnique ==
    /\ \A t, u \in Txns :
        (t # u /\ status[t] # "idle" /\ status[u] # "idle") => startTs[t] # startTs[u]
    /\ \A t, u \in Txns :
        (t # u /\ status[t] = "committed" /\ status[u] = "committed")
            => commitTs[t] # commitTs[u]
    /\ \A t \in Txns : status[t] = "committed" =>
        /\ commitTs[t] > startTs[t]
        /\ commitTs[t] <= clock
    /\ \A t \in Txns : \A u \in Txns :
        (status[t] = "committed" /\ status[u] # "idle") => commitTs[t] # startTs[u]

ClockMonotone == [][clock' > clock \/ clock' = clock]_vars

CommitTsStable ==
    [][\A t \in Txns : status[t] = "committed" =>
          (status'[t] = "committed" /\ commitTs'[t] = commitTs[t])]_vars

\* (1) Serializability: every committed transaction observed exactly the
\* state produced by the serial execution in commit-timestamp order.
Serializability ==
    \A t \in Txns : status[t] = "committed" =>
        /\ readDone[t] = rs[t]
        /\ \A k \in rs[t] : readVal[t][k] = SerialVal(k, commitTs[t])

\* (2) Atomicity: versions exist only for committed transactions, all at the
\* commit timestamp; uninstalled writes of a committed txn remain locked
\* (hence invisible to readers) until installed.
Atomicity ==
    /\ \A k \in Keys : \A v \in store[k] : v.txn # NoTxn =>
            /\ status[v.txn] = "committed"
            /\ k \in ws[v.txn]
            /\ v.ts = commitTs[v.txn]
            /\ v.val = wval[v.txn][k]
    /\ \A t \in Txns : status[t] = "committed" =>
            /\ primary[t] \in applied[t]
            /\ \A k \in ws[t] : k \in applied[t] \/ locks[k] = t
    /\ \A t \in Txns : status[t] \in {"aborted", "idle", "active"} =>
            \A k \in Keys : locks[k] # t

\* (3) No lost updates: versions of a key are totally ordered by timestamp,
\* and the latest installed version is the last committed writer's value.
NoLostUpdates ==
    /\ \A k \in Keys : \A v, w \in store[k] : v.ts = w.ts => v = w
    /\ \A k \in Keys : locks[k] = NoTxn =>
            LatestVersion(k).val = SerialVal(k, clock + 1)

\* (4) Read consistency: every value read is the state of the committed
\* prefix (by commit timestamp) up to the reader's snapshot.
ReadConsistency ==
    \A t \in Txns : status[t] # "idle" =>
        \A k \in readDone[t] : readVal[t][k] = SerialVal(k, startTs[t])

Safety ==
    /\ TypeOK
    /\ TimestampsUnique
    /\ Serializability
    /\ Atomicity
    /\ NoLostUpdates
    /\ ReadConsistency

-----------------------------------------------------------------------------
(* Liveness properties *)

\* Under fair scheduling and no permanent primary failure, every started
\* transaction eventually commits or aborts.
EventualDecision ==
    \A t \in Txns :
        status[t] \in {"active", "preparing"} ~> status[t] \in {"committed", "aborted"}

\* Every committed transaction eventually has all writes installed.
EventualApply ==
    \A t \in Txns : status[t] = "committed" ~> applied[t] = ws[t]

\* Every lock is eventually released.
LocksReleased ==
    \A k \in Keys : locks[k] # NoTxn ~> locks[k] = NoTxn

Liveness == EventualDecision /\ EventualApply /\ LocksReleased

THEOREM Spec => []Safety /\ ClockMonotone /\ CommitTsStable /\ Liveness
=============================================================================