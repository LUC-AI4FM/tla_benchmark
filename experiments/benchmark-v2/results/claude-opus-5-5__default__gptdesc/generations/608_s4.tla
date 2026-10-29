---------------------------- MODULE ResolvedTS ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS RM,      \* set of region keys
          MaxTS    \* bound on the timestamp oracle

ASSUME MaxTS \in Nat /\ RM # {}

VARIABLES
    tso,              \* global timestamp oracle
    regionState,      \* per-region transaction state
    regionStartTs,    \* start ts of the in-flight txn in each region
    regionMsgs,       \* per-region queue of generated, not yet applied msgs
    channel,          \* FIFO channel from regions to the resolver
    resolverLocks,    \* resolver-side tracked locks (start ts) per region
    lastResolved,     \* last resolved ts produced by the resolver
    resolvedTsQueue,  \* output queue of resolved timestamps
    commitTsQueue     \* output queue of commit timestamps

vars == << tso, regionState, regionStartTs, regionMsgs, channel,
           resolverLocks, lastResolved, resolvedTsQueue, commitTsQueue >>

TS == 0..MaxTS

PrewriteMsgs == [type : {"Prewrite"}, region : RM, startTs : TS]
CommitMsgs   == [type : {"Commit"}, region : RM, startTs : TS, commitTs : TS]
RollbackMsgs == [type : {"Rollback"}, region : RM, startTs : TS]
FetchTSMsgs  == [type : {"FetchTS"}, ts : TS]

RegionMsg == PrewriteMsgs \cup CommitMsgs \cup RollbackMsgs
Msg       == RegionMsg \cup FetchTSMsgs

CommitEntry == [ts : TS, resolved : TS]

Range(s) == { s[i] : i \in DOMAIN s }

-----------------------------------------------------------------------------
TypeOK ==
    /\ tso \in TS
    /\ regionState \in [RM -> {"idle", "prewrited"}]
    /\ regionStartTs \in [RM -> TS]
    /\ regionMsgs \in [RM -> Seq(RegionMsg)]
    /\ channel \in Seq(Msg)
    /\ resolverLocks \in [RM -> SUBSET TS]
    /\ lastResolved \in TS
    /\ resolvedTsQueue \in Seq(TS)
    /\ commitTsQueue \in Seq(CommitEntry)

Init ==
    /\ tso = 0
    /\ regionState = [r \in RM |-> "idle"]
    /\ regionStartTs = [r \in RM |-> 0]
    /\ regionMsgs = [r \in RM |-> << >>]
    /\ channel = << >>
    /\ resolverLocks = [r \in RM |-> {}]
    /\ lastResolved = 0
    /\ resolvedTsQueue = << >>
    /\ commitTsQueue = << >>

-----------------------------------------------------------------------------
(* Region-side transaction steps *)

Prewrite(r) ==
    /\ regionState[r] = "idle"
    /\ tso < MaxTS
    /\ tso' = tso + 1
    /\ regionState' = [regionState EXCEPT ![r] = "prewrited"]
    /\ regionStartTs' = [regionStartTs EXCEPT ![r] = tso + 1]
    /\ regionMsgs' = [regionMsgs EXCEPT ![r] =
          Append(@, [type |-> "Prewrite", region |-> r, startTs |-> tso + 1])]
    /\ UNCHANGED << channel, resolverLocks, lastResolved,
                    resolvedTsQueue, commitTsQueue >>

Commit(r) ==
    /\ regionState[r] = "prewrited"
    /\ tso < MaxTS
    /\ tso' = tso + 1
    /\ regionState' = [regionState EXCEPT ![r] = "idle"]
    /\ regionMsgs' = [regionMsgs EXCEPT ![r] =
          Append(@, [type |-> "Commit", region |-> r,
                     startTs |-> regionStartTs[r], commitTs |-> tso + 1])]
    /\ UNCHANGED << regionStartTs, channel, resolverLocks, lastResolved,
                    resolvedTsQueue, commitTsQueue >>

Rollback(r) ==
    /\ regionState[r] = "prewrited"
    /\ regionState' = [regionState EXCEPT ![r] = "idle"]
    /\ regionMsgs' = [regionMsgs EXCEPT ![r] =
          Append(@, [type |-> "Rollback", region |-> r,
                     startTs |-> regionStartTs[r]])]
    /\ UNCHANGED << tso, regionStartTs, channel, resolverLocks, lastResolved,
                    resolvedTsQueue, commitTsQueue >>

(* A region applies its oldest message and forwards it to the resolver *)
ApplyMsg(r) ==
    /\ regionMsgs[r] # << >>
    /\ channel' = Append(channel, Head(regionMsgs[r]))
    /\ regionMsgs' = [regionMsgs EXCEPT ![r] = Tail(@)]
    /\ UNCHANGED << tso, regionState, regionStartTs, resolverLocks,
                    lastResolved, resolvedTsQueue, commitTsQueue >>

(* A fetch-ts request: obtains a fresh ts once all regions have applied
   their pending messages, and sends a FetchTS message to the resolver. *)
FetchTS ==
    /\ tso < MaxTS
    /\ \A r \in RM : regionMsgs[r] = << >>
    /\ tso' = tso + 1
    /\ channel' = Append(channel, [type |-> "FetchTS", ts |-> tso + 1])
    /\ UNCHANGED << regionState, regionStartTs, regionMsgs, resolverLocks,
                    lastResolved, resolvedTsQueue, commitTsQueue >>

-----------------------------------------------------------------------------
(* Resolver-side handling *)

NoOutstandingPrewrite == \A r \in RM : resolverLocks[r] = {}

HandlePrewrite ==
    /\ channel # << >>
    /\ Head(channel).type = "Prewrite"
    /\ LET m == Head(channel) IN
         resolverLocks' = [resolverLocks EXCEPT ![m.region] = @ \cup {m.startTs}]
    /\ channel' = Tail(channel)
    /\ UNCHANGED << tso, regionState, regionStartTs, regionMsgs,
                    lastResolved, resolvedTsQueue, commitTsQueue >>

HandleCommit ==
    /\ channel # << >>
    /\ Head(channel).type = "Commit"
    /\ LET m == Head(channel) IN
         /\ resolverLocks' = [resolverLocks EXCEPT ![m.region] = @ \ {m.startTs}]
         /\ commitTsQueue' = Append(commitTsQueue,
                                    [ts |-> m.commitTs, resolved |-> lastResolved])
    /\ channel' = Tail(channel)
    /\ UNCHANGED << tso, regionState, regionStartTs, regionMsgs,
                    lastResolved, resolvedTsQueue >>

HandleRollback ==
    /\ channel # << >>
    /\ Head(channel).type = "Rollback"
    /\ LET m == Head(channel) IN
         resolverLocks' = [resolverLocks EXCEPT ![m.region] = @ \ {m.startTs}]
    /\ channel' = Tail(channel)
    /\ UNCHANGED << tso, regionState, regionStartTs, regionMsgs,
                    lastResolved, resolvedTsQueue, commitTsQueue >>

HandleFetchTS ==
    /\ channel # << >>
    /\ Head(channel).type = "FetchTS"
    /\ LET m == Head(channel) IN
         IF NoOutstandingPrewrite
           THEN /\ resolvedTsQueue' = Append(resolvedTsQueue, m.ts)
                /\ lastResolved' = m.ts
           ELSE UNCHANGED << resolvedTsQueue, lastResolved >>
    /\ channel' = Tail(channel)
    /\ UNCHANGED << tso, regionState, regionStartTs, regionMsgs,
                    resolverLocks, commitTsQueue >>

ResolverStep ==
    \/ HandlePrewrite
    \/ HandleCommit
    \/ HandleRollback
    \/ HandleFetchTS

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
(* Safety properties *)

\* Every commit ts emitted is strictly greater than any resolved ts
\* emitted before it.
CommitTSConsistency ==
    \A i \in DOMAIN commitTsQueue :
        commitTsQueue[i].ts > commitTsQueue[i].resolved

\* Resolved timestamps are strictly increasing, never exceed the oracle,
\* and the last one equals lastResolved.
ResolvedTSConsistency ==
    /\ \A i, j \in DOMAIN resolvedTsQueue :
          i < j => resolvedTsQueue[i] < resolvedTsQueue[j]
    /\ \A i \in DOMAIN resolvedTsQueue : resolvedTsQueue[i] <= tso
    /\ resolvedTsQueue # << >> =>
          resolvedTsQueue[Len(resolvedTsQueue)] = lastResolved

Safety == TypeOK /\ CommitTSConsistency /\ ResolvedTSConsistency

THEOREM Spec => [](TypeOK /\ CommitTSConsistency /\ ResolvedTSConsistency)

-----------------------------------------------------------------------------
(* Liveness: a FetchTS message at the head of the channel, when no region
   has an outstanding prewrite, eventually produces a resolved ts. *)

FetchAtHead(t) ==
    /\ channel # << >>
    /\ Head(channel).type = "FetchTS"
    /\ Head(channel).ts = t

FetchTSProducesResolvedTS ==
    \A t \in 1..MaxTS :
        (FetchAtHead(t) /\ NoOutstandingPrewrite) ~> (t \in Range(resolvedTsQueue))

THEOREM Spec => FetchTSProducesResolvedTS

=============================================================================