---------------------------- MODULE ResolvedTS ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT RM

\* Upper bound on the timestamp oracle, which keeps the state space finite.
MaxTS == 3
TS == 0..MaxTS

VARIABLES
    tso,            \* global timestamp oracle
    txn,            \* per-region transaction state
    pending,        \* per-region generated messages not yet applied
    regionLocks,    \* per-region applied locks (start ts)
    channel,        \* FIFO channel from regions to the resolver
    resolverLocks,  \* resolver's view of outstanding locks per region
    resolvedTS,     \* latest resolved ts per region at the resolver
    resolvedQ,      \* output queue of resolved timestamps
    commitQ         \* output queue of commit timestamps

vars == <<tso, txn, pending, regionLocks, channel, resolverLocks,
          resolvedTS, resolvedQ, commitQ>>

MsgTypes == {"Prewrite", "Commit", "Rollback", "FetchTS"}
Msgs == [type : MsgTypes, rm : RM, start : TS, commit : TS]
TxnState == [status : {"idle", "prewritten", "committed", "rolledback"},
             start : TS, commit : TS]

RTTypeOK ==
    /\ tso \in TS
    /\ txn \in [RM -> TxnState]
    /\ pending \in [RM -> Seq(Msgs)]
    /\ regionLocks \in [RM -> SUBSET TS]
    /\ channel \in Seq(Msgs)
    /\ resolverLocks \in [RM -> SUBSET TS]
    /\ resolvedTS \in [RM -> TS]
    /\ resolvedQ \in Seq([rm : RM, ts : TS])
    /\ commitQ \in Seq([rm : RM, start : TS, commit : TS, rts : TS])

Init ==
    /\ tso = 0
    /\ txn = [r \in RM |-> [status |-> "idle", start |-> 0, commit |-> 0]]
    /\ pending = [r \in RM |-> << >>]
    /\ regionLocks = [r \in RM |-> {}]
    /\ channel = << >>
    /\ resolverLocks = [r \in RM |-> {}]
    /\ resolvedTS = [r \in RM |-> 0]
    /\ resolvedQ = << >>
    /\ commitQ = << >>

-----------------------------------------------------------------------------
\* Region-local transaction steps (message generation)

Prewrite(r) ==
    /\ txn[r].status # "prewritten"
    /\ tso < MaxTS
    /\ tso' = tso + 1
    /\ txn' = [txn EXCEPT ![r] = [status |-> "prewritten", start |-> tso + 1, commit |-> 0]]
    /\ pending' = [pending EXCEPT ![r] =
          Append(@, [type |-> "Prewrite", rm |-> r, start |-> tso + 1, commit |-> 0])]
    /\ UNCHANGED <<regionLocks, channel, resolverLocks, resolvedTS, resolvedQ, commitQ>>

Commit(r) ==
    /\ txn[r].status = "prewritten"
    /\ tso < MaxTS
    /\ tso' = tso + 1
    /\ txn' = [txn EXCEPT ![r].status = "committed", ![r].commit = tso + 1]
    /\ pending' = [pending EXCEPT ![r] =
          Append(@, [type |-> "Commit", rm |-> r, start |-> txn[r].start, commit |-> tso + 1])]
    /\ UNCHANGED <<regionLocks, channel, resolverLocks, resolvedTS, resolvedQ, commitQ>>

Rollback(r) ==
    /\ txn[r].status = "prewritten"
    /\ txn' = [txn EXCEPT ![r].status = "rolledback"]
    /\ pending' = [pending EXCEPT ![r] =
          Append(@, [type |-> "Rollback", rm |-> r, start |-> txn[r].start, commit |-> 0])]
    /\ UNCHANGED <<tso, regionLocks, channel, resolverLocks, resolvedTS, resolvedQ, commitQ>>

FetchTS(r) ==
    /\ tso < MaxTS
    /\ tso' = tso + 1
    /\ pending' = [pending EXCEPT ![r] =
          Append(@, [type |-> "FetchTS", rm |-> r, start |-> tso + 1, commit |-> 0])]
    /\ UNCHANGED <<txn, regionLocks, channel, resolverLocks, resolvedTS, resolvedQ, commitQ>>

\* Apply a message locally in the region and forward it to the resolver channel
ApplyMsg(r) ==
    /\ pending[r] # << >>
    /\ LET m == Head(pending[r]) IN
         /\ regionLocks' = [regionLocks EXCEPT ![r] =
               IF m.type = "Prewrite" THEN @ \cup {m.start}
               ELSE IF m.type \in {"Commit", "Rollback"} THEN @ \ {m.start}
               ELSE @]
         /\ channel' = Append(channel, m)
    /\ pending' = [pending EXCEPT ![r] = Tail(@)]
    /\ UNCHANGED <<tso, txn, resolverLocks, resolvedTS, resolvedQ, commitQ>>

-----------------------------------------------------------------------------
\* Resolver-side handling

ResolverStep ==
    /\ channel # << >>
    /\ channel' = Tail(channel)
    /\ LET m == Head(channel)
           r == m.rm
       IN
         IF m.type = "Prewrite" THEN
             /\ resolverLocks' = [resolverLocks EXCEPT ![r] = @ \cup {m.start}]
             /\ UNCHANGED <<resolvedTS, resolvedQ, commitQ>>
         ELSE IF m.type = "Commit" THEN
             /\ resolverLocks' = [resolverLocks EXCEPT ![r] = @ \ {m.start}]
             /\ commitQ' = Append(commitQ, [rm |-> r, start |-> m.start,
                                            commit |-> m.commit, rts |-> resolvedTS[r]])
             /\ UNCHANGED <<resolvedTS, resolvedQ>>
         ELSE IF m.type = "Rollback" THEN
             /\ resolverLocks' = [resolverLocks EXCEPT ![r] = @ \ {m.start}]
             /\ UNCHANGED <<resolvedTS, resolvedQ, commitQ>>
         ELSE \* FetchTS
             /\ UNCHANGED <<resolverLocks, commitQ>>
             /\ IF resolverLocks[r] = {} /\ m.start > resolvedTS[r]
                   THEN /\ resolvedTS' = [resolvedTS EXCEPT ![r] = m.start]
                        /\ resolvedQ' = Append(resolvedQ, [rm |-> r, ts |-> m.start])
                   ELSE UNCHANGED <<resolvedTS, resolvedQ>>
    /\ UNCHANGED <<tso, txn, pending, regionLocks>>

\* Quiescent termination, which avoids spurious deadlock
Terminating ==
    /\ tso = MaxTS
    /\ \A r \in RM : txn[r].status # "prewritten" /\ pending[r] = << >>
    /\ channel = << >>
    /\ UNCHANGED vars

Next ==
    \/ \E r \in RM : Prewrite(r) \/ Commit(r) \/ Rollback(r) \/ FetchTS(r) \/ ApplyMsg(r)
    \/ ResolverStep
    \/ Terminating

RTSpec == Init /\ [][Next]_vars
          /\ \A r \in RM : WF_vars(ApplyMsg(r))
          /\ WF_vars(ResolverStep)

-----------------------------------------------------------------------------
\* Properties

CommitConsistency ==
    /\ \A i \in DOMAIN commitQ :
          /\ commitQ[i].commit > commitQ[i].start
          /\ commitQ[i].commit > commitQ[i].rts
    /\ \A i, j \in DOMAIN commitQ :
          i # j => commitQ[i].commit # commitQ[j].commit

ResolvedConsistency ==
    /\ \A i, j \in DOMAIN resolvedQ :
          (i < j /\ resolvedQ[i].rm = resolvedQ[j].rm) => resolvedQ[i].ts < resolvedQ[j].ts
    /\ \A r \in RM : \A l \in resolverLocks[r] : l > resolvedTS[r]

LiveCond ==
    /\ \E i \in DOMAIN channel : channel[i].type = "FetchTS"
    /\ \A i \in DOMAIN channel : channel[i].type = "FetchTS"
    /\ \A r \in RM : resolverLocks[r] = {}
    /\ \A r \in RM : txn[r].status # "prewritten"

ResolveLiveness == LiveCond ~> (Len(resolvedQ) > 0)

=============================================================================