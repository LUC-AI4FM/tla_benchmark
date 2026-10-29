---------------------------- MODULE ResolvedTs ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS RM,        \* set of region keys
          MaxTS      \* bound on the timestamp oracle (keeps the model finite)

ASSUME RM # {} /\ MaxTS \in Nat /\ MaxTS > 0

VARIABLES
    ts,              \* global timestamp oracle
    regionState,     \* per region: "idle" or "prewritten"
    startTs,         \* per region: start ts of the outstanding transaction
    regionMsgs,      \* per region: locally generated, not yet forwarded messages
    channel,         \* FIFO channel from regions to the resolver
    locks,           \* resolver view: outstanding prewrite start ts per region (0 = none)
    regionResolved,  \* resolver view: latest safe FetchTS ts per region
    lastResolved,    \* last resolved ts emitted by the resolver
    resolvedQ,       \* output queue of resolved timestamps
    commitQ,         \* output queue of commit records
    committed,       \* history: set of committed transactions (region side)
    fetched          \* history: set of timestamps obtained by FetchTS

vars == << ts, regionState, startTs, regionMsgs, channel, locks,
           regionResolved, lastResolved, resolvedQ, commitQ, committed, fetched >>

TSRange == 0..MaxTS

MsgTypes == {"Prewrite", "Commit", "Rollback", "FetchTS"}

Msg == [type : MsgTypes, region : RM, start : TSRange, commit : TSRange, ts : TSRange]

CommitRec == [region : RM, start : TSRange, commit : TSRange, resolved : TSRange]

TxnRec == [region : RM, start : TSRange, commit : TSRange]

Min(S) == CHOOSE x \in S : \A y \in S : x <= y
Max(a, b) == IF a >= b THEN a ELSE b

MkMsg(t, r, s, c, f) == [type |-> t, region |-> r, start |-> s, commit |-> c, ts |-> f]

-----------------------------------------------------------------------------
Init ==
    /\ ts = 0
    /\ regionState = [r \in RM |-> "idle"]
    /\ startTs = [r \in RM |-> 0]
    /\ regionMsgs = [r \in RM |-> << >>]
    /\ channel = << >>
    /\ locks = [r \in RM |-> 0]
    /\ regionResolved = [r \in RM |-> 0]
    /\ lastResolved = 0
    /\ resolvedQ = << >>
    /\ commitQ = << >>
    /\ committed = {}
    /\ fetched = {}

-----------------------------------------------------------------------------
\* Region-side transaction steps

Prewrite(r) ==
    /\ regionState[r] = "idle"
    /\ ts < MaxTS
    /\ ts' = ts + 1
    /\ regionState' = [regionState EXCEPT ![r] = "prewritten"]
    /\ startTs' = [startTs EXCEPT ![r] = ts + 1]
    /\ regionMsgs' = [regionMsgs EXCEPT ![r] =
                        Append(@, MkMsg("Prewrite", r, ts + 1, 0, 0))]
    /\ UNCHANGED << channel, locks, regionResolved, lastResolved,
                    resolvedQ, commitQ, committed, fetched >>

Commit(r) ==
    /\ regionState[r] = "prewritten"
    /\ ts < MaxTS
    /\ ts' = ts + 1
    /\ regionState' = [regionState EXCEPT ![r] = "idle"]
    /\ regionMsgs' = [regionMsgs EXCEPT ![r] =
                        Append(@, MkMsg("Commit", r, startTs[r], ts + 1, 0))]
    /\ committed' = committed \cup
                      {[region |-> r, start |-> startTs[r], commit |-> ts + 1]}
    /\ startTs' = [startTs EXCEPT ![r] = 0]
    /\ UNCHANGED << channel, locks, regionResolved, lastResolved,
                    resolvedQ, commitQ, fetched >>

Rollback(r) ==
    /\ regionState[r] = "prewritten"
    /\ regionState' = [regionState EXCEPT ![r] = "idle"]
    /\ regionMsgs' = [regionMsgs EXCEPT ![r] =
                        Append(@, MkMsg("Rollback", r, startTs[r], 0, 0))]
    /\ startTs' = [startTs EXCEPT ![r] = 0]
    /\ UNCHANGED << ts, channel, locks, regionResolved, lastResolved,
                    resolvedQ, commitQ, committed, fetched >>

\* Fetch a timestamp and ask every region to report it after its prior messages
FetchTS ==
    /\ ts < MaxTS
    /\ ts' = ts + 1
    /\ fetched' = fetched \cup {ts + 1}
    /\ regionMsgs' = [r \in RM |->
                        Append(regionMsgs[r], MkMsg("FetchTS", r, 0, 0, ts + 1))]
    /\ UNCHANGED << regionState, startTs, channel, locks, regionResolved,
                    lastResolved, resolvedQ, commitQ, committed >>

\* Apply a region-local message: forward it into the channel to the resolver
ApplyMsg(r) ==
    /\ regionMsgs[r] # << >>
    /\ channel' = Append(channel, Head(regionMsgs[r]))
    /\ regionMsgs' = [regionMsgs EXCEPT ![r] = Tail(@)]
    /\ UNCHANGED << ts, regionState, startTs, locks, regionResolved,
                    lastResolved, resolvedQ, commitQ, committed, fetched >>

-----------------------------------------------------------------------------
\* Resolver-side handling

HandlePrewrite ==
    /\ channel # << >>
    /\ Head(channel).type = "Prewrite"
    /\ LET m == Head(channel) IN
         locks' = [locks EXCEPT ![m.region] = m.start]
    /\ channel' = Tail(channel)
    /\ UNCHANGED << ts, regionState, startTs, regionMsgs, regionResolved,
                    lastResolved, resolvedQ, commitQ, committed, fetched >>

HandleCommit ==
    /\ channel # << >>
    /\ Head(channel).type = "Commit"
    /\ LET m == Head(channel) IN
         /\ locks' = [locks EXCEPT ![m.region] = 0]
         /\ commitQ' = Append(commitQ, [region   |-> m.region,
                                        start    |-> m.start,
                                        commit   |-> m.commit,
                                        resolved |-> lastResolved])
    /\ channel' = Tail(channel)
    /\ UNCHANGED << ts, regionState, startTs, regionMsgs, regionResolved,
                    lastResolved, resolvedQ, committed, fetched >>

HandleRollback ==
    /\ channel # << >>
    /\ Head(channel).type = "Rollback"
    /\ LET m == Head(channel) IN
         locks' = [locks EXCEPT ![m.region] = 0]
    /\ channel' = Tail(channel)
    /\ UNCHANGED << ts, regionState, startTs, regionMsgs, regionResolved,
                    lastResolved, resolvedQ, commitQ, committed, fetched >>

HandleFetchTS ==
    /\ channel # << >>
    /\ Head(channel).type = "FetchTS"
    /\ LET m == Head(channel) IN
         regionResolved' =
            IF locks[m.region] = 0
              THEN [regionResolved EXCEPT ![m.region] = Max(@, m.ts)]
              ELSE regionResolved
    /\ channel' = Tail(channel)
    /\ UNCHANGED << ts, regionState, startTs, regionMsgs, locks,
                    lastResolved, resolvedQ, commitQ, committed, fetched >>

HandleMsg == HandlePrewrite \/ HandleCommit \/ HandleRollback \/ HandleFetchTS

\* Produce a resolved timestamp into the output queue
EmitResolved ==
    LET m == Min({regionResolved[r] : r \in RM}) IN
      /\ m > lastResolved
      /\ lastResolved' = m
      /\ resolvedQ' = Append(resolvedQ, m)
      /\ UNCHANGED << ts, regionState, startTs, regionMsgs, channel, locks,
                      regionResolved, commitQ, committed, fetched >>

-----------------------------------------------------------------------------
Next ==
    \/ \E r \in RM : Prewrite(r) \/ Commit(r) \/ Rollback(r) \/ ApplyMsg(r)
    \/ FetchTS
    \/ HandleMsg
    \/ EmitResolved

Fairness ==
    /\ \A r \in RM : WF_vars(ApplyMsg(r))
    /\ WF_vars(HandleMsg)
    /\ WF_vars(EmitResolved)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety properties

TypeOK ==
    /\ ts \in TSRange
    /\ regionState \in [RM -> {"idle", "prewritten"}]
    /\ startTs \in [RM -> TSRange]
    /\ regionMsgs \in [RM -> Seq(Msg)]
    /\ channel \in Seq(Msg)
    /\ locks \in [RM -> TSRange]
    /\ regionResolved \in [RM -> TSRange]
    /\ lastResolved \in TSRange
    /\ resolvedQ \in Seq(TSRange)
    /\ commitQ \in Seq(CommitRec)
    /\ committed \subseteq TxnRec
    /\ fetched \subseteq TSRange

\* Every emitted commit ts is strictly greater than the resolved ts already
\* emitted, and every committed transaction with commit ts <= the resolved ts
\* has already been emitted to the commit queue.
CommitTsConsistency ==
    /\ \A i \in DOMAIN commitQ :
          /\ commitQ[i].commit > commitQ[i].resolved
          /\ commitQ[i].commit > commitQ[i].start
    /\ \A c \in committed :
          c.commit <= lastResolved =>
             \E i \in DOMAIN commitQ :
                /\ commitQ[i].region = c.region
                /\ commitQ[i].commit = c.commit

\* Resolved timestamps are strictly increasing and never exceed the oracle.
ResolvedTsConsistency ==
    /\ \A i, j \in DOMAIN resolvedQ : i < j => resolvedQ[i] < resolvedQ[j]
    /\ resolvedQ # << >> => resolvedQ[Len(resolvedQ)] = lastResolved
    /\ lastResolved <= ts

-----------------------------------------------------------------------------
\* Liveness: a fetched timestamp eventually becomes resolved when no region
\* has an outstanding prewrite.

NoOutstandingPrewrite == \A r \in RM : regionState[r] = "idle"

FetchTSProducesResolvedTs ==
    \A t \in 1..MaxTS :
        ((t \in fetched) /\ []NoOutstandingPrewrite) ~> (lastResolved >= t)

=============================================================================