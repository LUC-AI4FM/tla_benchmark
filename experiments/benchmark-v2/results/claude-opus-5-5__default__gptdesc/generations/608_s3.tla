---------------------------- MODULE ResolvedTS ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS RM,       \* set of region keys
          MaxTS     \* bound on the timestamp oracle (for model checking)

ASSUME MaxTS \in Nat /\ MaxTS > 0
ASSUME RM # {}

VARIABLES
    tso,            \* global timestamp oracle
    regionState,    \* per-region transaction state
    regionStart,    \* start ts of the current transaction in each region
    regionMsgs,     \* region-local generated, not yet applied, messages
    channel,        \* channel from regions to the resolver
    locks,          \* resolver-side set of outstanding lock start ts per region
    resolvedTs,     \* resolver-side resolved ts per region
    resolvedQueue,  \* output queue of resolved timestamps
    commitQueue     \* output queue of commit timestamps

vars == << tso, regionState, regionStart, regionMsgs, channel,
           locks, resolvedTs, resolvedQueue, commitQueue >>

TS == 0..MaxTS

MsgType == {"Prewrite", "Commit", "Rollback", "FetchTS"}

Msg == [type : MsgType, region : RM, startTs : TS, ts : TS]

ResolvedEntry == [region : RM, ts : TS]

CommitEntry == [region : RM, startTs : TS, commitTs : TS, rtsAtOutput : TS]

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

-----------------------------------------------------------------------------
TypeOK ==
    /\ tso \in TS
    /\ regionState \in [RM -> {"idle", "prewrote"}]
    /\ regionStart \in [RM -> TS]
    /\ regionMsgs \in [RM -> Seq(Msg)]
    /\ channel \in Seq(Msg)
    /\ locks \in [RM -> SUBSET TS]
    /\ resolvedTs \in [RM -> TS]
    /\ resolvedQueue \in Seq(ResolvedEntry)
    /\ commitQueue \in Seq(CommitEntry)

Init ==
    /\ tso = 0
    /\ regionState = [r \in RM |-> "idle"]
    /\ regionStart = [r \in RM |-> 0]
    /\ regionMsgs = [r \in RM |-> << >>]
    /\ channel = << >>
    /\ locks = [r \in RM |-> {}]
    /\ resolvedTs = [r \in RM |-> 0]
    /\ resolvedQueue = << >>
    /\ commitQueue = << >>

-----------------------------------------------------------------------------
\* Region-side transaction steps (message generation)

Prewrite(r) ==
    /\ regionState[r] = "idle"
    /\ tso < MaxTS
    /\ tso' = tso + 1
    /\ regionState' = [regionState EXCEPT ![r] = "prewrote"]
    /\ regionStart' = [regionStart EXCEPT ![r] = tso + 1]
    /\ regionMsgs' = [regionMsgs EXCEPT ![r] =
          Append(@, [type |-> "Prewrite", region |-> r,
                     startTs |-> tso + 1, ts |-> 0])]
    /\ UNCHANGED << channel, locks, resolvedTs, resolvedQueue, commitQueue >>

Commit(r) ==
    /\ regionState[r] = "prewrote"
    /\ tso < MaxTS
    /\ tso' = tso + 1
    /\ regionState' = [regionState EXCEPT ![r] = "idle"]
    /\ regionMsgs' = [regionMsgs EXCEPT ![r] =
          Append(@, [type |-> "Commit", region |-> r,
                     startTs |-> regionStart[r], ts |-> tso + 1])]
    /\ UNCHANGED << regionStart, channel, locks, resolvedTs,
                    resolvedQueue, commitQueue >>

Rollback(r) ==
    /\ regionState[r] = "prewrote"
    /\ regionState' = [regionState EXCEPT ![r] = "idle"]
    /\ regionMsgs' = [regionMsgs EXCEPT ![r] =
          Append(@, [type |-> "Rollback", region |-> r,
                     startTs |-> regionStart[r], ts |-> 0])]
    /\ UNCHANGED << tso, regionStart, channel, locks, resolvedTs,
                    resolvedQueue, commitQueue >>

\* Fetch a fresh timestamp from the oracle and enqueue it in region order
FetchTS(r) ==
    /\ tso < MaxTS
    /\ tso' = tso + 1
    /\ regionMsgs' = [regionMsgs EXCEPT ![r] =
          Append(@, [type |-> "FetchTS", region |-> r,
                     startTs |-> 0, ts |-> tso + 1])]
    /\ UNCHANGED << regionState, regionStart, channel, locks, resolvedTs,
                    resolvedQueue, commitQueue >>

\* Apply a region-local message and forward it through the channel
ApplyMsg(r) ==
    /\ regionMsgs[r] # << >>
    /\ channel' = Append(channel, Head(regionMsgs[r]))
    /\ regionMsgs' = [regionMsgs EXCEPT ![r] = Tail(@)]
    /\ UNCHANGED << tso, regionState, regionStart, locks, resolvedTs,
                    resolvedQueue, commitQueue >>

-----------------------------------------------------------------------------
\* Resolver-side handling

HandlePrewrite(m) ==
    /\ locks' = [locks EXCEPT ![m.region] = @ \cup {m.startTs}]
    /\ UNCHANGED << resolvedTs, resolvedQueue, commitQueue >>

HandleCommit(m) ==
    /\ locks' = [locks EXCEPT ![m.region] = @ \ {m.startTs}]
    /\ commitQueue' = Append(commitQueue,
          [region |-> m.region, startTs |-> m.startTs,
           commitTs |-> m.ts, rtsAtOutput |-> resolvedTs[m.region]])
    /\ UNCHANGED << resolvedTs, resolvedQueue >>

HandleRollback(m) ==
    /\ locks' = [locks EXCEPT ![m.region] = @ \ {m.startTs}]
    /\ UNCHANGED << resolvedTs, resolvedQueue, commitQueue >>

HandleFetchTS(m) ==
    LET r    == m.region
        cand == IF locks[r] = {} THEN m.ts ELSE Min(locks[r]) - 1
    IN
    /\ IF cand > resolvedTs[r]
         THEN /\ resolvedTs' = [resolvedTs EXCEPT ![r] = cand]
              /\ resolvedQueue' = Append(resolvedQueue,
                                         [region |-> r, ts |-> cand])
         ELSE UNCHANGED << resolvedTs, resolvedQueue >>
    /\ UNCHANGED << locks, commitQueue >>

HandleMsg ==
    /\ channel # << >>
    /\ LET m == Head(channel) IN
         /\ channel' = Tail(channel)
         /\ CASE m.type = "Prewrite" -> HandlePrewrite(m)
              [] m.type = "Commit"   -> HandleCommit(m)
              [] m.type = "Rollback" -> HandleRollback(m)
              [] m.type = "FetchTS"  -> HandleFetchTS(m)
    /\ UNCHANGED << tso, regionState, regionStart, regionMsgs >>

-----------------------------------------------------------------------------
Next ==
    \/ \E r \in RM : Prewrite(r) \/ Commit(r) \/ Rollback(r)
                     \/ FetchTS(r) \/ ApplyMsg(r)
    \/ HandleMsg

Fairness ==
    /\ \A r \in RM : WF_vars(ApplyMsg(r))
    /\ WF_vars(HandleMsg)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety properties

\* Every commit ts emitted is strictly greater than the resolved ts already
\* emitted for that region, and greater than its start ts.
CommitTSConsistency ==
    \A i \in 1..Len(commitQueue) :
        /\ commitQueue[i].commitTs > commitQueue[i].rtsAtOutput
        /\ commitQueue[i].commitTs > commitQueue[i].startTs

\* Resolved timestamps per region are strictly increasing in the output queue,
\* and no outstanding lock has a start ts at or below the resolved ts.
ResolvedTSConsistency ==
    /\ \A i, j \in 1..Len(resolvedQueue) :
          (i < j /\ resolvedQueue[i].region = resolvedQueue[j].region)
             => resolvedQueue[i].ts < resolvedQueue[j].ts
    /\ \A r \in RM : \A s \in locks[r] : s > resolvedTs[r]
    /\ \A r \in RM :
          regionState[r] = "prewrote" => regionStart[r] > resolvedTs[r]

Safety == TypeOK /\ CommitTSConsistency /\ ResolvedTSConsistency

-----------------------------------------------------------------------------
\* Liveness

NoOutstandingPrewrite ==
    \A r \in RM : regionState[r] # "prewrote" /\ locks[r] = {}

FetchTSPending(r, t) ==
    \/ \E i \in 1..Len(regionMsgs[r]) :
          regionMsgs[r][i].type = "FetchTS" /\ regionMsgs[r][i].ts = t
    \/ \E i \in 1..Len(channel) :
          /\ channel[i].type = "FetchTS"
          /\ channel[i].region = r
          /\ channel[i].ts = t

FetchTSLeadsToResolved ==
    \A r \in RM : \A t \in TS :
        (FetchTSPending(r, t) /\ NoOutstandingPrewrite)
            ~> (resolvedTs[r] >= t)

THEOREM Spec => []Safety
THEOREM Spec => FetchTSLeadsToResolved
=============================================================================