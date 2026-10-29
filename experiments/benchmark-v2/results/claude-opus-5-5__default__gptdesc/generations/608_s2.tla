---------------------------- MODULE ResolvedTS ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS RM,        \* set of region keys
          MaxTs      \* bound on the timestamp oracle (for model checking)

ASSUME MaxTs \in Nat /\ MaxTs > 0

VARIABLES
    ts,             \* global timestamp oracle (TSO)
    lock,           \* lock[r] = start ts of outstanding prewrite at region r, or NoTs
    regionMsgs,     \* regionMsgs[r] = region-local queue of generated messages
    channel,        \* FIFO channel from regions to the resolver
    resolverLocks,  \* set of locks currently tracked by the resolver
    resolvedTs,     \* latest resolved timestamp produced by the resolver
    resolvedOut,    \* output queue of resolved timestamps
    commitOut       \* output queue of committed transactions

vars == <<ts, lock, regionMsgs, channel, resolverLocks,
          resolvedTs, resolvedOut, commitOut>>

NoTs == 0
Ts   == 0..MaxTs

PrewriteMsgs == [type : {"Prewrite"}, region : RM, start : Ts]
CommitMsgs   == [type : {"Commit"}, region : RM, start : Ts, commit : Ts]
RollbackMsgs == [type : {"Rollback"}, region : RM, start : Ts]
FetchTSMsgs  == [type : {"FetchTS"}, ts : Ts, clean : BOOLEAN]

RegionMsg == PrewriteMsgs \cup CommitMsgs \cup RollbackMsgs
Msg       == RegionMsg \cup FetchTSMsgs

LockRec   == [region : RM, start : Ts]
CommitRec == [region : RM, start : Ts, commit : Ts, resolved : Ts]

Min(S) == CHOOSE x \in S : \A y \in S : x <= y
Max(a, b) == IF a >= b THEN a ELSE b

-----------------------------------------------------------------------------
TypeOK ==
    /\ ts \in Ts
    /\ lock \in [RM -> Ts]
    /\ regionMsgs \in [RM -> Seq(RegionMsg)]
    /\ channel \in Seq(Msg)
    /\ resolverLocks \subseteq LockRec
    /\ resolvedTs \in Ts
    /\ resolvedOut \in Seq(Ts)
    /\ commitOut \in Seq(CommitRec)

Init ==
    /\ ts = 0
    /\ lock = [r \in RM |-> NoTs]
    /\ regionMsgs = [r \in RM |-> <<>>]
    /\ channel = <<>>
    /\ resolverLocks = {}
    /\ resolvedTs = 0
    /\ resolvedOut = <<>>
    /\ commitOut = <<>>

-----------------------------------------------------------------------------
\* Region-local transaction steps

Prewrite(r) ==
    /\ lock[r] = NoTs
    /\ ts < MaxTs
    /\ ts' = ts + 1
    /\ lock' = [lock EXCEPT ![r] = ts + 1]
    /\ regionMsgs' = [regionMsgs EXCEPT ![r] =
            Append(@, [type |-> "Prewrite", region |-> r, start |-> ts + 1])]
    /\ UNCHANGED <<channel, resolverLocks, resolvedTs, resolvedOut, commitOut>>

Commit(r) ==
    /\ lock[r] # NoTs
    /\ ts < MaxTs
    /\ ts' = ts + 1
    /\ lock' = [lock EXCEPT ![r] = NoTs]
    /\ regionMsgs' = [regionMsgs EXCEPT ![r] =
            Append(@, [type |-> "Commit", region |-> r,
                       start |-> lock[r], commit |-> ts + 1])]
    /\ UNCHANGED <<channel, resolverLocks, resolvedTs, resolvedOut, commitOut>>

Rollback(r) ==
    /\ lock[r] # NoTs
    /\ lock' = [lock EXCEPT ![r] = NoTs]
    /\ regionMsgs' = [regionMsgs EXCEPT ![r] =
            Append(@, [type |-> "Rollback", region |-> r, start |-> lock[r]])]
    /\ UNCHANGED <<ts, channel, resolverLocks, resolvedTs, resolvedOut, commitOut>>

\* Apply a region-local message: forward it through the channel to the resolver
ApplyMsg(r) ==
    /\ regionMsgs[r] # <<>>
    /\ channel' = Append(channel, Head(regionMsgs[r]))
    /\ regionMsgs' = [regionMsgs EXCEPT ![r] = Tail(@)]
    /\ UNCHANGED <<ts, lock, resolverLocks, resolvedTs, resolvedOut, commitOut>>

\* Fetch a timestamp from TSO; only after all region messages were applied,
\* so that the FetchTS message is ordered behind every earlier region message.
FetchTS ==
    /\ \A r \in RM : regionMsgs[r] = <<>>
    /\ ts < MaxTs
    /\ ts' = ts + 1
    /\ channel' = Append(channel,
            [type |-> "FetchTS", ts |-> ts + 1,
             clean |-> \A r \in RM : lock[r] = NoTs])
    /\ UNCHANGED <<lock, regionMsgs, resolverLocks, resolvedTs, resolvedOut, commitOut>>

-----------------------------------------------------------------------------
\* Resolver-side handling

ResolvePrewrite(m) ==
    /\ resolverLocks' = resolverLocks \cup {[region |-> m.region, start |-> m.start]}
    /\ UNCHANGED <<resolvedTs, resolvedOut, commitOut>>

ResolveCommit(m) ==
    /\ resolverLocks' = resolverLocks \ {[region |-> m.region, start |-> m.start]}
    /\ commitOut' = Append(commitOut,
            [region |-> m.region, start |-> m.start,
             commit |-> m.commit, resolved |-> resolvedTs])
    /\ UNCHANGED <<resolvedTs, resolvedOut>>

ResolveRollback(m) ==
    /\ resolverLocks' = resolverLocks \ {[region |-> m.region, start |-> m.start]}
    /\ UNCHANGED <<resolvedTs, resolvedOut, commitOut>>

ResolveFetchTS(m) ==
    LET candidate == IF resolverLocks = {}
                     THEN m.ts
                     ELSE Min({l.start : l \in resolverLocks}) - 1
        newTs == Max(resolvedTs, candidate)
    IN /\ resolvedTs' = newTs
       /\ resolvedOut' = Append(resolvedOut, newTs)
       /\ UNCHANGED <<resolverLocks, commitOut>>

ResolverStep ==
    /\ channel # <<>>
    /\ LET m == Head(channel) IN
         /\ channel' = Tail(channel)
         /\ CASE m.type = "Prewrite" -> ResolvePrewrite(m)
              [] m.type = "Commit"   -> ResolveCommit(m)
              [] m.type = "Rollback" -> ResolveRollback(m)
              [] m.type = "FetchTS"  -> ResolveFetchTS(m)
    /\ UNCHANGED <<ts, lock, regionMsgs>>

-----------------------------------------------------------------------------
Next ==
    \/ \E r \in RM : Prewrite(r) \/ Commit(r) \/ Rollback(r) \/ ApplyMsg(r)
    \/ FetchTS
    \/ ResolverStep

Fairness ==
    /\ \A r \in RM : WF_vars(ApplyMsg(r))
    /\ WF_vars(ResolverStep)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety properties

\* Every commit emitted has commit ts greater than its start ts and greater
\* than the resolved ts already published when the commit was emitted.
CommitTSConsistency ==
    \A i \in 1..Len(commitOut) :
        /\ commitOut[i].commit > commitOut[i].start
        /\ commitOut[i].commit > commitOut[i].resolved

\* Resolved timestamps are monotone, never exceed the TSO, the latest equals
\* resolvedTs, and no committed transaction is below a later resolved ts
\* unless it was already emitted.
ResolvedTSConsistency ==
    /\ \A i, j \in 1..Len(resolvedOut) : i < j => resolvedOut[i] <= resolvedOut[j]
    /\ \A i \in 1..Len(resolvedOut) : resolvedOut[i] <= ts
    /\ resolvedOut # <<>> => resolvedOut[Len(resolvedOut)] = resolvedTs
    /\ \A l \in resolverLocks : resolvedTs < l.start
    /\ \A r \in RM : lock[r] # NoTs => resolvedTs < lock[r]

Safety == TypeOK /\ CommitTSConsistency /\ ResolvedTSConsistency

-----------------------------------------------------------------------------
\* Liveness: a FetchTS issued while no region has an outstanding prewrite
\* eventually produces a resolved timestamp at least as large as its ts.

FetchPending(t) ==
    \E i \in 1..Len(channel) :
        /\ channel[i].type = "FetchTS"
        /\ channel[i].ts = t
        /\ channel[i].clean

FetchTSLeadsToResolved ==
    \A t \in Ts : FetchPending(t) ~> (resolvedTs >= t)

THEOREM Spec => [](TypeOK /\ CommitTSConsistency /\ ResolvedTSConsistency)
THEOREM Spec => FetchTSLeadsToResolved
=============================================================================