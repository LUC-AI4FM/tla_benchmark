---------------------------- MODULE ResolvedTS ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS RM,      \* set of region keys
          MaxTS    \* upper bound on timestamps (keeps the model finite)

ASSUME MaxTS \in Nat /\ MaxTS > 0
ASSUME RM # {}

VARIABLES
    tso,           \* global timestamp oracle
    regionTxn,     \* region-local transaction state
    regionStart,   \* start ts of the region's current transaction
    regionMsgs,    \* region-local generated, not yet applied messages
    channel,       \* channel forwarding applied messages to the resolver
    resolverLock,  \* resolver's view of outstanding locks per region
    resolvedQ,     \* output queue of resolved timestamps
    commitQ,       \* output queue of commit timestamps
    outSeq         \* global output sequence number (orders both queues)

vars == <<tso, regionTxn, regionStart, regionMsgs, channel,
          resolverLock, resolvedQ, commitQ, outSeq>>

NoLock == 0

MsgTypes == {"Prewrite", "Commit", "Rollback", "FetchTS"}

Msg == [type : MsgTypes, region : RM, ts : 0..MaxTS, cts : 0..MaxTS]

OutEntry == [region : RM, ts : 0..MaxTS, seq : Nat]

-----------------------------------------------------------------------------
TypeOK ==
    /\ tso \in 0..MaxTS
    /\ regionTxn \in [RM -> {"none", "prewrited"}]
    /\ regionStart \in [RM -> 0..MaxTS]
    /\ regionMsgs \in [RM -> Seq(Msg)]
    /\ channel \in Seq(Msg)
    /\ resolverLock \in [RM -> 0..MaxTS]
    /\ resolvedQ \in Seq(OutEntry)
    /\ commitQ \in Seq(OutEntry)
    /\ outSeq \in Nat

Init ==
    /\ tso = 0
    /\ regionTxn = [r \in RM |-> "none"]
    /\ regionStart = [r \in RM |-> 0]
    /\ regionMsgs = [r \in RM |-> <<>>]
    /\ channel = <<>>
    /\ resolverLock = [r \in RM |-> NoLock]
    /\ resolvedQ = <<>>
    /\ commitQ = <<>>
    /\ outSeq = 0

-----------------------------------------------------------------------------
(* Region-local transaction steps *)

Prewrite(r) ==
    /\ regionTxn[r] = "none"
    /\ tso < MaxTS
    /\ tso' = tso + 1
    /\ regionTxn' = [regionTxn EXCEPT ![r] = "prewrited"]
    /\ regionStart' = [regionStart EXCEPT ![r] = tso + 1]
    /\ regionMsgs' = [regionMsgs EXCEPT ![r] =
          Append(@, [type |-> "Prewrite", region |-> r, ts |-> tso + 1, cts |-> 0])]
    /\ UNCHANGED <<channel, resolverLock, resolvedQ, commitQ, outSeq>>

Commit(r) ==
    /\ regionTxn[r] = "prewrited"
    /\ tso < MaxTS
    /\ tso' = tso + 1
    /\ regionTxn' = [regionTxn EXCEPT ![r] = "none"]
    /\ regionMsgs' = [regionMsgs EXCEPT ![r] =
          Append(@, [type |-> "Commit", region |-> r,
                     ts |-> regionStart[r], cts |-> tso + 1])]
    /\ UNCHANGED <<regionStart, channel, resolverLock, resolvedQ, commitQ, outSeq>>

Rollback(r) ==
    /\ regionTxn[r] = "prewrited"
    /\ regionTxn' = [regionTxn EXCEPT ![r] = "none"]
    /\ regionMsgs' = [regionMsgs EXCEPT ![r] =
          Append(@, [type |-> "Rollback", region |-> r,
                     ts |-> regionStart[r], cts |-> 0])]
    /\ UNCHANGED <<tso, regionStart, channel, resolverLock, resolvedQ, commitQ, outSeq>>

FetchTS(r) ==
    /\ tso < MaxTS
    /\ tso' = tso + 1
    /\ regionMsgs' = [regionMsgs EXCEPT ![r] =
          Append(@, [type |-> "FetchTS", region |-> r, ts |-> tso + 1, cts |-> 0])]
    /\ UNCHANGED <<regionTxn, regionStart, channel, resolverLock,
                   resolvedQ, commitQ, outSeq>>

(* Apply a region-local message: forward it through the channel *)
ApplyMsg(r) ==
    /\ regionMsgs[r] # <<>>
    /\ channel' = Append(channel, Head(regionMsgs[r]))
    /\ regionMsgs' = [regionMsgs EXCEPT ![r] = Tail(@)]
    /\ UNCHANGED <<tso, regionTxn, regionStart, resolverLock,
                   resolvedQ, commitQ, outSeq>>

-----------------------------------------------------------------------------
(* Resolver-side handling *)

HandlePrewrite(m) ==
    /\ resolverLock' = [resolverLock EXCEPT ![m.region] = m.ts]
    /\ UNCHANGED <<resolvedQ, commitQ, outSeq>>

HandleCommit(m) ==
    /\ resolverLock' = [resolverLock EXCEPT ![m.region] = NoLock]
    /\ commitQ' = Append(commitQ, [region |-> m.region, ts |-> m.cts, seq |-> outSeq])
    /\ outSeq' = outSeq + 1
    /\ UNCHANGED resolvedQ

HandleRollback(m) ==
    /\ resolverLock' = [resolverLock EXCEPT ![m.region] = NoLock]
    /\ UNCHANGED <<resolvedQ, commitQ, outSeq>>

HandleFetchTS(m) ==
    /\ IF resolverLock[m.region] = NoLock
          THEN /\ resolvedQ' = Append(resolvedQ,
                                 [region |-> m.region, ts |-> m.ts, seq |-> outSeq])
               /\ outSeq' = outSeq + 1
          ELSE UNCHANGED <<resolvedQ, outSeq>>
    /\ UNCHANGED <<resolverLock, commitQ>>

ResolverStep ==
    /\ channel # <<>>
    /\ LET m == Head(channel) IN
         /\ channel' = Tail(channel)
         /\ \/ (m.type = "Prewrite" /\ HandlePrewrite(m))
            \/ (m.type = "Commit"   /\ HandleCommit(m))
            \/ (m.type = "Rollback" /\ HandleRollback(m))
            \/ (m.type = "FetchTS"  /\ HandleFetchTS(m))
    /\ UNCHANGED <<tso, regionTxn, regionStart, regionMsgs>>

-----------------------------------------------------------------------------
Next ==
    \/ \E r \in RM : Prewrite(r) \/ Commit(r) \/ Rollback(r)
                     \/ FetchTS(r) \/ ApplyMsg(r)
    \/ ResolverStep

Fairness ==
    /\ \A r \in RM : WF_vars(ApplyMsg(r))
    /\ WF_vars(ResolverStep)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

\* Any commit ts emitted after a resolved ts for the same region is larger.
CommitTSConsistency ==
    \A i \in DOMAIN commitQ, j \in DOMAIN resolvedQ :
        (/\ commitQ[i].region = resolvedQ[j].region
         /\ resolvedQ[j].seq < commitQ[i].seq)
        => commitQ[i].ts > resolvedQ[j].ts

\* Resolved timestamps for each region are strictly increasing.
ResolvedTSConsistency ==
    \A i, j \in DOMAIN resolvedQ :
        (i < j /\ resolvedQ[i].region = resolvedQ[j].region)
        => resolvedQ[i].ts < resolvedQ[j].ts

Safety == TypeOK /\ CommitTSConsistency /\ ResolvedTSConsistency

-----------------------------------------------------------------------------
(* Liveness *)

FetchPending(r, t) ==
    \/ \E i \in DOMAIN regionMsgs[r] :
          regionMsgs[r][i].type = "FetchTS" /\ regionMsgs[r][i].ts = t
    \/ \E i \in DOMAIN channel :
          /\ channel[i].type = "FetchTS"
          /\ channel[i].region = r
          /\ channel[i].ts = t

NoOutstandingPrewrite ==
    /\ \A r \in RM : resolverLock[r] = NoLock
    /\ \A r \in RM : \A i \in DOMAIN regionMsgs[r] : regionMsgs[r][i].type # "Prewrite"
    /\ \A i \in DOMAIN channel : channel[i].type # "Prewrite"

ResolvedProduced(r, t) ==
    \E i \in DOMAIN resolvedQ : resolvedQ[i].region = r /\ resolvedQ[i].ts = t

FetchTSProgress ==
    \A r \in RM, t \in 1..MaxTS :
        (FetchPending(r, t) /\ NoOutstandingPrewrite) ~> ResolvedProduced(r, t)

THEOREM Spec => [](TypeOK /\ CommitTSConsistency /\ ResolvedTSConsistency)
THEOREM Spec => FetchTSProgress
=============================================================================