---- MODULE TimestampResolver ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT RM

MaxTS == 5

TSRange == 0..MaxTS

MsgTypes == {"Prewrite", "Commit", "Rollback", "FetchTS"}

AnyRM == CHOOSE r \in RM : TRUE

Msg == [type : MsgTypes, rm : RM, ts : TSRange]

RMStates == {"init", "prewrited", "committed", "rolledback"}

VARIABLES
    rmState,      \* region-local transaction state
    rmTentTS,     \* region-local tentative (prewrite) timestamp
    rmCommitTS,   \* region-local commit timestamp
    gts,          \* global timestamp generator
    channel,      \* ordered channel from regions to resolver
    minTS,        \* resolver's view of each region's minimum prepared ts (0 = none)
    resolvedQ,    \* output queue of resolved timestamps with output index
    outputQ       \* output queue of commit timestamps

vars == <<rmState, rmTentTS, rmCommitTS, gts, channel, minTS, resolvedQ, outputQ>>

SetMin(S) == CHOOSE x \in S : \A y \in S : x <= y
Max2(a, b) == IF a >= b THEN a ELSE b

LastResolved == IF Len(resolvedQ) = 0 THEN 0 ELSE resolvedQ[Len(resolvedQ)].ts

IsSeqOf(s, S) == /\ DOMAIN s = 1..Len(s)
                 /\ \A i \in 1..Len(s) : s[i] \in S

RTTypeOK ==
    /\ rmState \in [RM -> RMStates]
    /\ rmTentTS \in [RM -> TSRange]
    /\ rmCommitTS \in [RM -> TSRange]
    /\ gts \in TSRange
    /\ minTS \in [RM -> TSRange]
    /\ IsSeqOf(channel, Msg)
    /\ IsSeqOf(outputQ, TSRange)
    /\ IsSeqOf(resolvedQ, [ts : TSRange, idx : Nat])

Init ==
    /\ rmState = [r \in RM |-> "init"]
    /\ rmTentTS = [r \in RM |-> 0]
    /\ rmCommitTS = [r \in RM |-> 0]
    /\ gts = 0
    /\ channel = <<>>
    /\ minTS = [r \in RM |-> 0]
    /\ resolvedQ = <<>>
    /\ outputQ = <<>>

\* Region actions: each applies locally and forwards the event atomically,
\* so a Commit/Rollback can never precede the local application of its Prewrite.
Prewrite(r) ==
    /\ rmState[r] \in {"init", "committed", "rolledback"}
    /\ gts < MaxTS
    /\ gts' = gts + 1
    /\ rmState' = [rmState EXCEPT ![r] = "prewrited"]
    /\ rmTentTS' = [rmTentTS EXCEPT ![r] = gts + 1]
    /\ rmCommitTS' = [rmCommitTS EXCEPT ![r] = 0]
    /\ channel' = Append(channel, [type |-> "Prewrite", rm |-> r, ts |-> gts + 1])
    /\ UNCHANGED <<minTS, resolvedQ, outputQ>>

Commit(r) ==
    /\ rmState[r] = "prewrited"
    /\ gts < MaxTS
    /\ gts' = gts + 1
    /\ rmState' = [rmState EXCEPT ![r] = "committed"]
    /\ rmCommitTS' = [rmCommitTS EXCEPT ![r] = gts + 1]
    /\ channel' = Append(channel, [type |-> "Commit", rm |-> r, ts |-> gts + 1])
    /\ UNCHANGED <<rmTentTS, minTS, resolvedQ, outputQ>>

Rollback(r) ==
    /\ rmState[r] = "prewrited"
    /\ rmState' = [rmState EXCEPT ![r] = "rolledback"]
    /\ rmTentTS' = [rmTentTS EXCEPT ![r] = 0]
    /\ channel' = Append(channel, [type |-> "Rollback", rm |-> r, ts |-> rmTentTS[r]])
    /\ UNCHANGED <<gts, rmCommitTS, minTS, resolvedQ, outputQ>>

FetchTS ==
    /\ gts < MaxTS
    /\ gts' = gts + 1
    /\ channel' = Append(channel, [type |-> "FetchTS", rm |-> AnyRM, ts |-> gts + 1])
    /\ UNCHANGED <<rmState, rmTentTS, rmCommitTS, minTS, resolvedQ, outputQ>>

\* Resolver processes the head of the channel in order.
Resolve ==
    /\ Len(channel) > 0
    /\ LET m == Head(channel) IN
       /\ channel' = Tail(channel)
       /\ CASE m.type = "Prewrite" ->
                /\ minTS' = [minTS EXCEPT ![m.rm] =
                              IF minTS[m.rm] = 0 THEN m.ts
                              ELSE IF m.ts < minTS[m.rm] THEN m.ts ELSE minTS[m.rm]]
                /\ UNCHANGED <<resolvedQ, outputQ>>
            [] m.type = "Commit" ->
                /\ minTS' = [minTS EXCEPT ![m.rm] = 0]
                /\ outputQ' = Append(outputQ, m.ts)
                /\ UNCHANGED resolvedQ
            [] m.type = "Rollback" ->
                /\ minTS' = [minTS EXCEPT ![m.rm] = 0]
                /\ UNCHANGED <<resolvedQ, outputQ>>
            [] m.type = "FetchTS" ->
                LET pending == {minTS[r] : r \in {x \in RM : minTS[x] # 0}}
                    cand == SetMin(pending \cup {m.ts})
                    newR == Max2(cand, LastResolved)
                IN /\ resolvedQ' = Append(resolvedQ, [ts |-> newR, idx |-> Len(outputQ) + 1])
                   /\ UNCHANGED <<minTS, outputQ>>
    /\ UNCHANGED <<rmState, rmTentTS, rmCommitTS, gts>>

Done ==
    /\ gts = MaxTS
    /\ channel = <<>>
    /\ \A r \in RM : rmState[r] # "prewrited"
    /\ UNCHANGED vars

Next ==
    \/ \E r \in RM : Prewrite(r) \/ Commit(r) \/ Rollback(r)
    \/ FetchTS
    \/ Resolve
    \/ Done

RTSpec == Init /\ [][Next]_vars /\ WF_vars(Resolve)

CommitConsistency ==
    \A r \in RM :
        rmState[r] = "committed" =>
            \/ rmTentTS[r] < rmCommitTS[r]
            \/ (rmTentTS[r] = 0 /\ rmCommitTS[r] = 0)

ResolvedConsistency ==
    \A i \in 1..Len(resolvedQ) :
        \A j \in resolvedQ[i].idx..Len(outputQ) :
            resolvedQ[i].ts < outputQ[j]

ResolveLiveness ==
    ( /\ \A r \in RM : minTS[r] = 0
      /\ \E i \in 1..Len(channel) : channel[i].type = "FetchTS" )
    ~> (LastResolved > 0)

====