------------------------------ MODULE ResolvedTS ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS RM,        \* set of keys in the region
          MaxTs      \* bound on the global timestamp oracle (for model checking)

ASSUME MaxTs \in Nat

VARIABLES
    key_prewritten,      \* [RM -> BOOLEAN]
    key_committed,       \* [RM -> BOOLEAN]
    key_prewrite_ts,     \* [RM -> TS]
    key_commit_ts,       \* [RM -> TS]
    key_data,            \* [RM -> Seq(Msg)] per-key message log
    key_apply_offset,    \* [RM -> Nat] how much of the log has been forwarded
    resolver_min_ts,     \* [RM -> TS] min prewrite ts per key (0 = none)
    next_ts,             \* global timestamp counter (TSO)
    channel,             \* forwarding channel to the resolver
    resolved_ts,         \* output queue of resolved timestamps
    commit_ts            \* output queue of commit timestamps

key_vars == <<key_prewritten, key_committed, key_prewrite_ts, key_commit_ts,
              key_data, key_apply_offset>>
vars == <<key_prewritten, key_committed, key_prewrite_ts, key_commit_ts,
          key_data, key_apply_offset, resolver_min_ts, next_ts, channel,
          resolved_ts, commit_ts>>

TS == 0..MaxTs
NoTS == 0
SomeKey == CHOOSE k \in RM : TRUE

MsgTypes == {"prewrite", "commit", "rollback", "fetch"}
Msg == [type : MsgTypes, key : RM, ts : TS]

\* Each resolved timestamp records how many commit timestamps had been
\* output at the time it was produced, so that "subsequent" commits can
\* be identified.
ResolvedEntry == [ts : TS, commitLen : Nat]

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

-----------------------------------------------------------------------------
RTTypeOK ==
    /\ key_prewritten \in [RM -> BOOLEAN]
    /\ key_committed \in [RM -> BOOLEAN]
    /\ key_prewrite_ts \in [RM -> TS]
    /\ key_commit_ts \in [RM -> TS]
    /\ key_data \in [RM -> Seq(Msg)]
    /\ key_apply_offset \in [RM -> Nat]
    /\ \A k \in RM : key_apply_offset[k] <= Len(key_data[k])
    /\ resolver_min_ts \in [RM -> TS]
    /\ next_ts \in TS
    /\ channel \in Seq(Msg)
    /\ resolved_ts \in Seq(ResolvedEntry)
    /\ commit_ts \in Seq(TS)

-----------------------------------------------------------------------------
Init ==
    /\ key_prewritten = [k \in RM |-> FALSE]
    /\ key_committed = [k \in RM |-> FALSE]
    /\ key_prewrite_ts = [k \in RM |-> NoTS]
    /\ key_commit_ts = [k \in RM |-> NoTS]
    /\ key_data = [k \in RM |-> <<>>]
    /\ key_apply_offset = [k \in RM |-> 0]
    /\ resolver_min_ts = [k \in RM |-> NoTS]
    /\ next_ts = 0
    /\ channel = <<>>
    /\ resolved_ts = <<>>
    /\ commit_ts = <<>>

-----------------------------------------------------------------------------
(* Transaction actions on keys *)

\* Optimistic prewrite: start_ts is a freshly allocated timestamp.
OptimisticPrewrite(k) ==
    /\ ~key_prewritten[k]
    /\ ~key_committed[k]
    /\ next_ts + 1 <= MaxTs
    /\ LET ts == next_ts + 1 IN
        /\ next_ts' = ts
        /\ key_prewritten' = [key_prewritten EXCEPT ![k] = TRUE]
        /\ key_prewrite_ts' = [key_prewrite_ts EXCEPT ![k] = ts]
        /\ key_data' = [key_data EXCEPT ![k] =
                          Append(@, [type |-> "prewrite", key |-> k, ts |-> ts])]
    /\ UNCHANGED <<key_committed, key_commit_ts, key_apply_offset,
                   resolver_min_ts, channel, resolved_ts, commit_ts>>

\* Pessimistic prewrite: the transaction first obtains a start_ts and then a
\* for_update_ts; the prewrite is recorded with the for_update_ts.
PessimisticPrewrite(k) ==
    /\ ~key_prewritten[k]
    /\ ~key_committed[k]
    /\ next_ts + 2 <= MaxTs
    /\ LET for_update_ts == next_ts + 2 IN
        /\ next_ts' = for_update_ts
        /\ key_prewritten' = [key_prewritten EXCEPT ![k] = TRUE]
        /\ key_prewrite_ts' = [key_prewrite_ts EXCEPT ![k] = for_update_ts]
        /\ key_data' = [key_data EXCEPT ![k] =
                          Append(@, [type |-> "prewrite", key |-> k,
                                     ts |-> for_update_ts])]
    /\ UNCHANGED <<key_committed, key_commit_ts, key_apply_offset,
                   resolver_min_ts, channel, resolved_ts, commit_ts>>

Commit(k) ==
    /\ key_prewritten[k]
    /\ ~key_committed[k]
    /\ next_ts + 1 <= MaxTs
    /\ LET ts == next_ts + 1 IN
        /\ next_ts' = ts
        /\ key_committed' = [key_committed EXCEPT ![k] = TRUE]
        /\ key_prewritten' = [key_prewritten EXCEPT ![k] = FALSE]
        /\ key_commit_ts' = [key_commit_ts EXCEPT ![k] = ts]
        /\ key_data' = [key_data EXCEPT ![k] =
                          Append(@, [type |-> "commit", key |-> k, ts |-> ts])]
    /\ UNCHANGED <<key_prewrite_ts, key_apply_offset, resolver_min_ts,
                   channel, resolved_ts, commit_ts>>

Rollback(k) ==
    /\ key_prewritten[k]
    /\ ~key_committed[k]
    /\ key_prewritten' = [key_prewritten EXCEPT ![k] = FALSE]
    /\ key_prewrite_ts' = [key_prewrite_ts EXCEPT ![k] = NoTS]
    /\ key_data' = [key_data EXCEPT ![k] =
                      Append(@, [type |-> "rollback", key |-> k,
                                 ts |-> key_prewrite_ts[k]])]
    /\ UNCHANGED <<key_committed, key_commit_ts, key_apply_offset,
                   resolver_min_ts, next_ts, channel, resolved_ts, commit_ts>>

\* Forward the next un-applied message of key k to the central channel.
Apply(k) ==
    /\ key_apply_offset[k] < Len(key_data[k])
    /\ channel' = Append(channel, key_data[k][key_apply_offset[k] + 1])
    /\ key_apply_offset' = [key_apply_offset EXCEPT ![k] = @ + 1]
    /\ UNCHANGED <<key_prewritten, key_committed, key_prewrite_ts,
                   key_commit_ts, key_data, resolver_min_ts, next_ts,
                   resolved_ts, commit_ts>>

\* Periodically query the TSO and send the fetched timestamp to the resolver.
FetchTS ==
    /\ next_ts + 1 <= MaxTs
    /\ LET ts == next_ts + 1 IN
        /\ next_ts' = ts
        /\ channel' = Append(channel, [type |-> "fetch", key |-> SomeKey, ts |-> ts])
    /\ UNCHANGED <<key_vars, resolver_min_ts, resolved_ts, commit_ts>>

-----------------------------------------------------------------------------
(* Resolver *)

ActivePrewriteTs == { resolver_min_ts[k] : k \in {r \in RM : resolver_min_ts[r] # NoTS} }

TryResolve(fetched) ==
    LET rts == Min(ActivePrewriteTs \cup {fetched}) IN
        resolved_ts' = Append(resolved_ts, [ts |-> rts, commitLen |-> Len(commit_ts)])

HandlePrewrite(msg) ==
    /\ resolver_min_ts' = [resolver_min_ts EXCEPT ![msg.key] = msg.ts]
    /\ UNCHANGED <<resolved_ts, commit_ts>>

HandleCommit(msg) ==
    /\ resolver_min_ts' = [resolver_min_ts EXCEPT ![msg.key] = NoTS]
    /\ commit_ts' = Append(commit_ts, msg.ts)
    /\ UNCHANGED resolved_ts

HandleRollback(msg) ==
    /\ resolver_min_ts' = [resolver_min_ts EXCEPT ![msg.key] = NoTS]
    /\ UNCHANGED <<resolved_ts, commit_ts>>

HandleFetch(msg) ==
    /\ TryResolve(msg.ts)
    /\ UNCHANGED <<resolver_min_ts, commit_ts>>

Resolve ==
    /\ channel # <<>>
    /\ LET msg == Head(channel) IN
        /\ channel' = Tail(channel)
        /\ CASE msg.type = "prewrite" -> HandlePrewrite(msg)
             [] msg.type = "commit"   -> HandleCommit(msg)
             [] msg.type = "rollback" -> HandleRollback(msg)
             [] msg.type = "fetch"    -> HandleFetch(msg)
    /\ UNCHANGED <<key_vars, next_ts>>

-----------------------------------------------------------------------------
\* Allow stuttering once the system has quiesced (avoids spurious deadlock).
Terminated ==
    /\ channel = <<>>
    /\ \A k \in RM : key_apply_offset[k] = Len(key_data[k])
    /\ next_ts + 1 > MaxTs
    /\ UNCHANGED vars

Next ==
    \/ \E k \in RM :
        \/ OptimisticPrewrite(k)
        \/ PessimisticPrewrite(k)
        \/ Commit(k)
        \/ Rollback(k)
        \/ Apply(k)
    \/ FetchTS
    \/ Resolve
    \/ Terminated

Fairness ==
    /\ WF_vars(Resolve)
    /\ \A k \in RM : WF_vars(Apply(k))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

CommitConsistency ==
    \A k \in RM :
        key_committed[k] => key_commit_ts[k] > key_prewrite_ts[k]

ResolvedConsistency ==
    \A i \in 1..Len(resolved_ts) :
        \A j \in 1..Len(commit_ts) :
            j > resolved_ts[i].commitLen => resolved_ts[i].ts < commit_ts[j]

(* Liveness property *)

NoActivePrewrite == \A k \in RM : resolver_min_ts[k] = NoTS

FetchPending == \E i \in 1..Len(channel) : channel[i].type = "fetch"

ResolveLiveness ==
    (NoActivePrewrite /\ FetchPending) ~> (Len(resolved_ts) > 0)

THEOREM Spec => [](RTTypeOK /\ CommitConsistency /\ ResolvedConsistency)
THEOREM Spec => ResolveLiveness
=============================================================================