--------------------------- MODULE ResolvedTimestamp ---------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Regions,        \* set of regions
    MaxTS,          \* bound on the global timestamp generator (for model checking)
    MaxChan         \* bound on the channel length (for model checking)

ASSUME /\ Regions # {}
       /\ MaxTS \in Nat \ {0}
       /\ MaxChan \in Nat \ {0}

NoRegion == "none"

VARIABLES
    globalTS,       \* global timestamp generator (last issued timestamp)
    regionState,    \* per-region transaction phase
    tentativeTS,    \* per-region tentative (prewrite) timestamp, 0 = none
    commitTS,       \* per-region commit timestamp, 0 = none
    channel,        \* ordered asynchronous channel: region events and FetchTS
    minPrepared,    \* resolver: per-region minimum prepared timestamp, 0 = none
    lastResolved,   \* resolver: last (monotonic) resolved timestamp
    resolvedQ,      \* output queue of resolved timestamps with output index
    outputQ         \* output queue of commit timestamps

vars == << globalTS, regionState, tentativeTS, commitTS, channel,
           minPrepared, lastResolved, resolvedQ, outputQ >>

regionVars   == << regionState, tentativeTS, commitTS >>
resolverVars == << minPrepared, lastResolved, resolvedQ, outputQ >>

TS == 0..MaxTS

States == {"idle", "prewriting", "prewritten", "committed", "rolledback"}

MsgTypes == {"Prewrite", "Commit", "Rollback", "FetchTS"}

Msg == [type : MsgTypes, region : Regions \cup {NoRegion}, ts : TS]

ResolvedEntry == [ts : TS, idx : Nat \ {0}]

SetMin(S) == CHOOSE x \in S : \A y \in S : x <= y
Min(a, b) == IF a <= b THEN a ELSE b
Max(a, b) == IF a >= b THEN a ELSE b

-----------------------------------------------------------------------------
Init ==
    /\ globalTS = 0
    /\ regionState = [r \in Regions |-> "idle"]
    /\ tentativeTS = [r \in Regions |-> 0]
    /\ commitTS = [r \in Regions |-> 0]
    /\ channel = << >>
    /\ minPrepared = [r \in Regions |-> 0]
    /\ lastResolved = 0
    /\ resolvedQ = << >>
    /\ outputQ = << >>

-----------------------------------------------------------------------------
\* Region actions

\* A region starts a new transaction: it obtains a tentative timestamp.
\* Only allowed when no previous prewrite is outstanding.
StartPrewrite(r) ==
    /\ regionState[r] \in {"idle", "committed", "rolledback"}
    /\ globalTS < MaxTS
    /\ globalTS' = globalTS + 1
    /\ tentativeTS' = [tentativeTS EXCEPT ![r] = globalTS + 1]
    /\ commitTS' = [commitTS EXCEPT ![r] = 0]
    /\ regionState' = [regionState EXCEPT ![r] = "prewriting"]
    /\ UNCHANGED << channel, resolverVars >>

\* The prewrite is applied locally and the event is forwarded to the resolver.
ApplyPrewrite(r) ==
    /\ regionState[r] = "prewriting"
    /\ Len(channel) < MaxChan
    /\ channel' = Append(channel,
                    [type |-> "Prewrite", region |-> r, ts |-> tentativeTS[r]])
    /\ regionState' = [regionState EXCEPT ![r] = "prewritten"]
    /\ UNCHANGED << globalTS, tentativeTS, commitTS, resolverVars >>

\* Commit is only possible after the prewrite has been applied.
Commit(r) ==
    /\ regionState[r] = "prewritten"
    /\ globalTS < MaxTS
    /\ Len(channel) < MaxChan
    /\ globalTS' = globalTS + 1
    /\ commitTS' = [commitTS EXCEPT ![r] = globalTS + 1]
    /\ regionState' = [regionState EXCEPT ![r] = "committed"]
    /\ channel' = Append(channel,
                    [type |-> "Commit", region |-> r, ts |-> globalTS + 1])
    /\ UNCHANGED << tentativeTS, resolverVars >>

\* Rollback is only possible after the prewrite has been applied.
Rollback(r) ==
    /\ regionState[r] = "prewritten"
    /\ Len(channel) < MaxChan
    /\ channel' = Append(channel,
                    [type |-> "Rollback", region |-> r, ts |-> tentativeTS[r]])
    /\ tentativeTS' = [tentativeTS EXCEPT ![r] = 0]
    /\ commitTS' = [commitTS EXCEPT ![r] = 0]
    /\ regionState' = [regionState EXCEPT ![r] = "rolledback"]
    /\ UNCHANGED << globalTS, resolverVars >>

\* Sample the global timestamp generator and send a FetchTS request.
FetchTS ==
    /\ globalTS < MaxTS
    /\ Len(channel) < MaxChan
    /\ globalTS' = globalTS + 1
    /\ channel' = Append(channel,
                    [type |-> "FetchTS", region |-> NoRegion, ts |-> globalTS + 1])
    /\ UNCHANGED << regionVars, resolverVars >>

-----------------------------------------------------------------------------
\* Resolver

PendingRegions == {r \in Regions : minPrepared[r] # 0}

\* Combine minimum prepared timestamps (min policy) with the fetched
\* timestamp, then apply a max policy against the last resolved timestamp
\* so that resolved timestamps are globally monotonic.
ComputeResolved(fetched) ==
    LET candidate ==
          IF PendingRegions = {}
            THEN fetched
            ELSE Min(fetched, SetMin({minPrepared[r] : r \in PendingRegions}))
    IN  Max(lastResolved, candidate)

ResolverStep ==
    /\ channel # << >>
    /\ LET m == Head(channel) IN
         /\ channel' = Tail(channel)
         /\ CASE m.type = "Prewrite" ->
                   /\ minPrepared' = [minPrepared EXCEPT ![m.region] =
                          IF @ = 0 THEN m.ts ELSE Min(@, m.ts)]
                   /\ UNCHANGED << lastResolved, resolvedQ, outputQ >>
              [] m.type = "Commit" ->
                   /\ minPrepared' = [minPrepared EXCEPT ![m.region] = 0]
                   /\ outputQ' = Append(outputQ, m.ts)
                   /\ UNCHANGED << lastResolved, resolvedQ >>
              [] m.type = "Rollback" ->
                   /\ minPrepared' = [minPrepared EXCEPT ![m.region] = 0]
                   /\ UNCHANGED << lastResolved, resolvedQ, outputQ >>
              [] m.type = "FetchTS" ->
                   LET newRes == ComputeResolved(m.ts) IN
                   /\ lastResolved' = newRes
                   /\ resolvedQ' = Append(resolvedQ,
                                     [ts |-> newRes, idx |-> Len(outputQ) + 1])
                   /\ UNCHANGED << minPrepared, outputQ >>
    /\ UNCHANGED << globalTS, regionVars >>

-----------------------------------------------------------------------------
Next ==
    \/ \E r \in Regions :
         \/ StartPrewrite(r)
         \/ ApplyPrewrite(r)
         \/ Commit(r)
         \/ Rollback(r)
    \/ FetchTS
    \/ ResolverStep

Fairness == WF_vars(ResolverStep)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety invariants

TypeOK ==
    /\ globalTS \in TS
    /\ regionState \in [Regions -> States]
    /\ tentativeTS \in [Regions -> TS]
    /\ commitTS \in [Regions -> TS]
    /\ channel \in Seq(Msg)
    /\ Len(channel) <= MaxChan
    /\ minPrepared \in [Regions -> TS]
    /\ lastResolved \in TS
    /\ resolvedQ \in Seq(ResolvedEntry)
    /\ outputQ \in Seq(TS)

StateOK ==
    \A r \in Regions :
      /\ regionState[r] \in {"prewriting", "prewritten"} =>
            /\ tentativeTS[r] # 0
            /\ commitTS[r] = 0
      /\ regionState[r] = "rolledback" =>
            tentativeTS[r] = 0 /\ commitTS[r] = 0
      /\ tentativeTS[r] <= globalTS
      /\ commitTS[r] <= globalTS

CommitConsistency ==
    \A r \in Regions :
      regionState[r] = "committed" =>
        \/ tentativeTS[r] < commitTS[r]
        \/ tentativeTS[r] = 0 /\ commitTS[r] = 0

ResolvedConsistency ==
    \A k \in 1..Len(resolvedQ) :
      \A i \in resolvedQ[k].idx..Len(outputQ) :
        resolvedQ[k].ts < outputQ[i]

ResolvedMonotonic ==
    \A k \in 1..Len(resolvedQ) :
      \A j \in k..Len(resolvedQ) : resolvedQ[k].ts <= resolvedQ[j].ts

Invariants ==
    /\ TypeOK
    /\ StateOK
    /\ CommitConsistency
    /\ ResolvedConsistency
    /\ ResolvedMonotonic

\* Action property: the resolved timestamp never decreases
ResolvedNeverDecreases == [][lastResolved' >= lastResolved]_vars

-----------------------------------------------------------------------------
\* Liveness

FetchInChannel == \E i \in 1..Len(channel) : channel[i].type = "FetchTS"

NoPendingPrepared == \A r \in Regions : minPrepared[r] = 0

ResolvedProgress ==
    (NoPendingPrepared /\ FetchInChannel) ~> (lastResolved # 0)

=============================================================================