------------------------------ MODULE ResolvedTS ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT RM

MaxTS  == 6
MaxLog == 4

VARIABLES
    ts,                \* global timestamp oracle counter
    keyPrewritten,     \* key -> BOOLEAN
    keyCommitted,      \* key -> BOOLEAN
    keyPrewriteTS,     \* key -> start ts
    keyCommitTS,       \* key -> commit ts
    keyLog,            \* key -> sequence of messages
    keyApplied,        \* key -> applied offset into keyLog
    minPrewriteTS,     \* resolver: key -> min active prewrite ts (0 = none)
    channel,           \* forwarding channel to the resolver
    resolvedTSQueue,   \* output: resolved timestamps
    commitTSQueue,     \* output: commit timestamps
    fetchCount         \* number of FetchTS requests issued

vars == << ts, keyPrewritten, keyCommitted, keyPrewriteTS, keyCommitTS,
           keyLog, keyApplied, minPrewriteTS, channel, resolvedTSQueue,
           commitTSQueue, fetchCount >>

TSRange == 0..MaxTS

KeyMsg   == [type : {"prewrite", "commit", "rollback"}, key : RM,
             start : TSRange, commit : TSRange]
FetchMsg == [type : {"fetch"}, ts : TSRange]
Msg      == KeyMsg \cup FetchMsg

ResolvedEntry == [ts : TSRange, pos : Nat]

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

RTTypeOK ==
    /\ ts \in TSRange
    /\ keyPrewritten \in [RM -> BOOLEAN]
    /\ keyCommitted \in [RM -> BOOLEAN]
    /\ keyPrewriteTS \in [RM -> TSRange]
    /\ keyCommitTS \in [RM -> TSRange]
    /\ keyLog \in [RM -> Seq(KeyMsg)]
    /\ keyApplied \in [RM -> Nat]
    /\ \A k \in RM : keyApplied[k] <= Len(keyLog[k])
    /\ minPrewriteTS \in [RM -> TSRange]
    /\ channel \in Seq(Msg)
    /\ resolvedTSQueue \in Seq(ResolvedEntry)
    /\ commitTSQueue \in Seq(TSRange)
    /\ fetchCount \in Nat

RTInit ==
    /\ ts = 0
    /\ keyPrewritten = [k \in RM |-> FALSE]
    /\ keyCommitted = [k \in RM |-> FALSE]
    /\ keyPrewriteTS = [k \in RM |-> 0]
    /\ keyCommitTS = [k \in RM |-> 0]
    /\ keyLog = [k \in RM |-> << >>]
    /\ keyApplied = [k \in RM |-> 0]
    /\ minPrewriteTS = [k \in RM |-> 0]
    /\ channel = << >>
    /\ resolvedTSQueue = << >>
    /\ commitTSQueue = << >>
    /\ fetchCount = 0

ResolverUnchanged == UNCHANGED << minPrewriteTS, resolvedTSQueue, commitTSQueue >>

\* Optimistic prewrite: obtains a fresh start ts from the oracle.
OptimisticPrewrite(k) ==
    /\ ~keyPrewritten[k]
    /\ ts < MaxTS
    /\ Len(keyLog[k]) < MaxLog
    /\ ts' = ts + 1
    /\ keyPrewritten' = [keyPrewritten EXCEPT ![k] = TRUE]
    /\ keyCommitted' = [keyCommitted EXCEPT ![k] = FALSE]
    /\ keyPrewriteTS' = [keyPrewriteTS EXCEPT ![k] = ts + 1]
    /\ keyCommitTS' = [keyCommitTS EXCEPT ![k] = 0]
    /\ keyLog' = [keyLog EXCEPT ![k] = Append(@,
                    [type |-> "prewrite", key |-> k, start |-> ts + 1, commit |-> 0])]
    /\ UNCHANGED << keyApplied, channel, fetchCount >>
    /\ ResolverUnchanged

\* Pessimistic prewrite: uses the current (already allocated) ts as start ts.
PessimisticPrewrite(k) ==
    /\ ~keyPrewritten[k]
    /\ ts > 0
    /\ ts < MaxTS
    /\ Len(keyLog[k]) < MaxLog
    /\ keyPrewritten' = [keyPrewritten EXCEPT ![k] = TRUE]
    /\ keyCommitted' = [keyCommitted EXCEPT ![k] = FALSE]
    /\ keyPrewriteTS' = [keyPrewriteTS EXCEPT ![k] = ts]
    /\ keyCommitTS' = [keyCommitTS EXCEPT ![k] = 0]
    /\ keyLog' = [keyLog EXCEPT ![k] = Append(@,
                    [type |-> "prewrite", key |-> k, start |-> ts, commit |-> 0])]
    /\ UNCHANGED << ts, keyApplied, channel, fetchCount >>
    /\ ResolverUnchanged

Commit(k) ==
    /\ keyPrewritten[k]
    /\ ts < MaxTS
    /\ Len(keyLog[k]) < MaxLog
    /\ ts' = ts + 1
    /\ keyPrewritten' = [keyPrewritten EXCEPT ![k] = FALSE]
    /\ keyCommitted' = [keyCommitted EXCEPT ![k] = TRUE]
    /\ keyCommitTS' = [keyCommitTS EXCEPT ![k] = ts + 1]
    /\ keyLog' = [keyLog EXCEPT ![k] = Append(@,
                    [type |-> "commit", key |-> k,
                     start |-> keyPrewriteTS[k], commit |-> ts + 1])]
    /\ UNCHANGED << keyPrewriteTS, keyApplied, channel, fetchCount >>
    /\ ResolverUnchanged

Rollback(k) ==
    /\ keyPrewritten[k]
    /\ Len(keyLog[k]) < MaxLog
    /\ keyPrewritten' = [keyPrewritten EXCEPT ![k] = FALSE]
    /\ keyLog' = [keyLog EXCEPT ![k] = Append(@,
                    [type |-> "rollback", key |-> k,
                     start |-> keyPrewriteTS[k], commit |-> 0])]
    /\ UNCHANGED << ts, keyCommitted, keyPrewriteTS, keyCommitTS,
                    keyApplied, channel, fetchCount >>
    /\ ResolverUnchanged

Apply(k) ==
    /\ keyApplied[k] < Len(keyLog[k])
    /\ channel' = Append(channel, keyLog[k][keyApplied[k] + 1])
    /\ keyApplied' = [keyApplied EXCEPT ![k] = @ + 1]
    /\ UNCHANGED << ts, keyPrewritten, keyCommitted, keyPrewriteTS,
                    keyCommitTS, keyLog, fetchCount >>
    /\ ResolverUnchanged

\* Query the TSO; the request is ordered after all previously logged writes.
FetchTS ==
    /\ ts < MaxTS
    /\ \A k \in RM : keyApplied[k] = Len(keyLog[k])
    /\ ts' = ts + 1
    /\ channel' = Append(channel, [type |-> "fetch", ts |-> ts + 1])
    /\ fetchCount' = fetchCount + 1
    /\ UNCHANGED << keyPrewritten, keyCommitted, keyPrewriteTS, keyCommitTS,
                    keyLog, keyApplied >>
    /\ ResolverUnchanged

TryResolve(f) ==
    LET active == {minPrewriteTS[k] : k \in {j \in RM : minPrewriteTS[j] # 0}}
        newTS  == Min(active \cup {f})
    IN  /\ resolvedTSQueue' = Append(resolvedTSQueue,
                                [ts |-> newTS, pos |-> Len(commitTSQueue)])
        /\ UNCHANGED << minPrewriteTS, commitTSQueue >>

ResolverHandle ==
    /\ channel # << >>
    /\ LET m == Head(channel) IN
       /\ channel' = Tail(channel)
       /\ IF m.type = "prewrite"
            THEN /\ minPrewriteTS' = [minPrewriteTS EXCEPT ![m.key] = m.start]
                 /\ UNCHANGED << resolvedTSQueue, commitTSQueue >>
          ELSE IF m.type = "commit"
            THEN /\ minPrewriteTS' = [minPrewriteTS EXCEPT ![m.key] = 0]
                 /\ commitTSQueue' = Append(commitTSQueue, m.commit)
                 /\ UNCHANGED resolvedTSQueue
          ELSE IF m.type = "rollback"
            THEN /\ minPrewriteTS' = [minPrewriteTS EXCEPT ![m.key] = 0]
                 /\ UNCHANGED << resolvedTSQueue, commitTSQueue >>
          ELSE TryResolve(m.ts)
    /\ UNCHANGED << ts, keyPrewritten, keyCommitted, keyPrewriteTS,
                    keyCommitTS, keyLog, keyApplied, fetchCount >>

Terminating ==
    /\ channel = << >>
    /\ \A k \in RM : keyApplied[k] = Len(keyLog[k])
    /\ UNCHANGED vars

RTNext ==
    \/ \E k \in RM : \/ OptimisticPrewrite(k)
                     \/ PessimisticPrewrite(k)
                     \/ Commit(k)
                     \/ Rollback(k)
                     \/ Apply(k)
    \/ FetchTS
    \/ ResolverHandle
    \/ Terminating

RTSpec ==
    /\ RTInit
    /\ [][RTNext]_vars
    /\ WF_vars(ResolverHandle)
    /\ \A k \in RM : WF_vars(Apply(k))

-----------------------------------------------------------------------------
\* Safety

CommitConsistency ==
    \A k \in RM : keyCommitted[k] => keyCommitTS[k] > keyPrewriteTS[k]

ResolvedConsistency ==
    \A i \in 1..Len(resolvedTSQueue) :
        \A j \in 1..Len(commitTSQueue) :
            j > resolvedTSQueue[i].pos => resolvedTSQueue[i].ts < commitTSQueue[j]

\* Liveness

ResolveLiveness ==
    ((\A k \in RM : minPrewriteTS[k] = 0) /\ fetchCount > 0)
        ~> (Len(resolvedTSQueue) > 0)

=============================================================================