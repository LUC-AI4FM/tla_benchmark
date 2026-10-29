------------------------------ MODULE ResolvedTs ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    KEYS,          \* set of keys (resources) in the region
    MAX_TIME,      \* bound on the timestamp oracle (for model checking)
    MODES          \* subset of {"optimistic", "pessimistic"}

ASSUME MAX_TIME \in Nat /\ MAX_TIME > 0
ASSUME MODES \subseteq {"optimistic", "pessimistic"} /\ MODES # {}

VARIABLES
    oracle,        \* timestamp oracle, monotonically increasing
    keyState,      \* [KEYS -> {"init","locking","prewritten","committed","rolledback"}]
    lockTs,        \* [KEYS -> Nat] prewrite timestamp of each key (0 = none)
    commitTs,      \* [KEYS -> Nat] commit timestamp of each key (0 = none)
    channel,       \* FIFO message channel to the resolver
    pending,       \* resolver view: [KEYS -> Nat] tracked prewrite ts (0 = none)
    output,        \* output queue of commit timestamps
    resolvedTs,    \* last computed resolved timestamp (0 = none yet)
    resolvedPos,   \* position in output at which resolvedTs was recorded
    fetched        \* TRUE iff a timestamp fetch message has been processed

vars == << oracle, keyState, lockTs, commitTs, channel, pending,
           output, resolvedTs, resolvedPos, fetched >>

Msg == [type : {"prewrite", "commit", "rollback"}, key : KEYS, ts : 0..MAX_TIME]
       \cup [type : {"fetch"}, ts : 0..MAX_TIME]

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

TypeOK ==
    /\ oracle \in 0..MAX_TIME
    /\ keyState \in [KEYS -> {"init", "locking", "prewritten", "committed", "rolledback"}]
    /\ lockTs \in [KEYS -> 0..MAX_TIME]
    /\ commitTs \in [KEYS -> 0..MAX_TIME]
    /\ channel \in Seq(Msg)
    /\ pending \in [KEYS -> 0..MAX_TIME]
    /\ output \in Seq(0..MAX_TIME)
    /\ resolvedTs \in 0..MAX_TIME
    /\ resolvedPos \in Nat
    /\ fetched \in BOOLEAN

Init ==
    /\ oracle = 0
    /\ keyState = [k \in KEYS |-> "init"]
    /\ lockTs = [k \in KEYS |-> 0]
    /\ commitTs = [k \in KEYS |-> 0]
    /\ channel = << >>
    /\ pending = [k \in KEYS |-> 0]
    /\ output = << >>
    /\ resolvedTs = 0
    /\ resolvedPos = 0
    /\ fetched = FALSE

-----------------------------------------------------------------------------
\* Transaction side

\* Optimistic prewrite: prewrite ts freshly obtained from the oracle.
PrewriteOptimistic(k) ==
    /\ "optimistic" \in MODES
    /\ keyState[k] = "init"
    /\ oracle < MAX_TIME
    /\ oracle' = oracle + 1
    /\ lockTs' = [lockTs EXCEPT ![k] = oracle + 1]
    /\ keyState' = [keyState EXCEPT ![k] = "locking"]
    /\ UNCHANGED << commitTs, channel, pending, output, resolvedTs, resolvedPos, fetched >>

\* Pessimistic prewrite: prewrite ts may be stale (obtained earlier).
PrewritePessimistic(k) ==
    /\ "pessimistic" \in MODES
    /\ keyState[k] = "init"
    /\ oracle > 0
    /\ \E t \in 1..oracle :
         lockTs' = [lockTs EXCEPT ![k] = t]
    /\ keyState' = [keyState EXCEPT ![k] = "locking"]
    /\ UNCHANGED << oracle, commitTs, channel, pending, output, resolvedTs, resolvedPos, fetched >>

\* The prewrite is applied and its event is sent to the resolver.
ApplyPrewrite(k) ==
    /\ keyState[k] = "locking"
    /\ keyState' = [keyState EXCEPT ![k] = "prewritten"]
    /\ channel' = Append(channel, [type |-> "prewrite", key |-> k, ts |-> lockTs[k]])
    /\ UNCHANGED << oracle, lockTs, commitTs, pending, output, resolvedTs, resolvedPos, fetched >>

\* Commit only after the prewrite has been fully applied.
Commit(k) ==
    /\ keyState[k] = "prewritten"
    /\ oracle < MAX_TIME
    /\ oracle' = oracle + 1
    /\ commitTs' = [commitTs EXCEPT ![k] = oracle + 1]
    /\ keyState' = [keyState EXCEPT ![k] = "committed"]
    /\ channel' = Append(channel, [type |-> "commit", key |-> k, ts |-> oracle + 1])
    /\ UNCHANGED << lockTs, pending, output, resolvedTs, resolvedPos, fetched >>

\* Rollback of an applied prewrite: event is sent to the resolver.
Rollback(k) ==
    /\ keyState[k] = "prewritten"
    /\ keyState' = [keyState EXCEPT ![k] = "rolledback"]
    /\ channel' = Append(channel, [type |-> "rollback", key |-> k, ts |-> lockTs[k]])
    /\ UNCHANGED << oracle, lockTs, commitTs, pending, output, resolvedTs, resolvedPos, fetched >>

\* Rollback before the prewrite was applied: nothing reaches the resolver.
AbortLocking(k) ==
    /\ keyState[k] = "locking"
    /\ keyState' = [keyState EXCEPT ![k] = "rolledback"]
    /\ UNCHANGED << oracle, lockTs, commitTs, channel, pending, output, resolvedTs, resolvedPos, fetched >>

\* A finalized key becomes free for a new transaction.
Reset(k) ==
    /\ keyState[k] \in {"committed", "rolledback"}
    /\ keyState' = [keyState EXCEPT ![k] = "init"]
    /\ lockTs' = [lockTs EXCEPT ![k] = 0]
    /\ commitTs' = [commitTs EXCEPT ![k] = 0]
    /\ UNCHANGED << oracle, channel, pending, output, resolvedTs, resolvedPos, fetched >>

\* Fetch a timestamp from the oracle and send it to the resolver.
FetchTs ==
    /\ oracle < MAX_TIME
    /\ oracle' = oracle + 1
    /\ channel' = Append(channel, [type |-> "fetch", ts |-> oracle + 1])
    /\ UNCHANGED << keyState, lockTs, commitTs, pending, output, resolvedTs, resolvedPos, fetched >>

-----------------------------------------------------------------------------
\* Resolver side: processes messages sequentially, in order.

PendingSet == { pending[k] : k \in { j \in KEYS : pending[j] # 0 } }

ResolverStep ==
    /\ channel # << >>
    /\ LET m == Head(channel) IN
       /\ channel' = Tail(channel)
       /\ CASE m.type = "prewrite" ->
                 /\ pending' = [pending EXCEPT ![m.key] = m.ts]
                 /\ UNCHANGED << output, resolvedTs, resolvedPos, fetched >>
            [] m.type = "commit" ->
                 /\ pending' = [pending EXCEPT ![m.key] = 0]
                 /\ output' = Append(output, m.ts)
                 /\ UNCHANGED << resolvedTs, resolvedPos, fetched >>
            [] m.type = "rollback" ->
                 /\ pending' = [pending EXCEPT ![m.key] = 0]
                 /\ UNCHANGED << output, resolvedTs, resolvedPos, fetched >>
            [] m.type = "fetch" ->
                 LET newTs == IF PendingSet = {}
                              THEN m.ts
                              ELSE Min(PendingSet \cup {m.ts})
                 IN /\ fetched' = TRUE
                    /\ IF newTs > resolvedTs
                         THEN /\ resolvedTs' = newTs
                              /\ resolvedPos' = Len(output)
                         ELSE UNCHANGED << resolvedTs, resolvedPos >>
                    /\ UNCHANGED << pending, output >>
    /\ UNCHANGED << oracle, keyState, lockTs, commitTs >>

-----------------------------------------------------------------------------

Next ==
    \/ \E k \in KEYS :
         \/ PrewriteOptimistic(k)
         \/ PrewritePessimistic(k)
         \/ ApplyPrewrite(k)
         \/ Commit(k)
         \/ Rollback(k)
         \/ AbortLocking(k)
         \/ Reset(k)
    \/ FetchTs
    \/ ResolverStep

Spec == Init /\ [][Next]_vars /\ WF_vars(Next) /\ WF_vars(ResolverStep)

-----------------------------------------------------------------------------
\* Safety properties

CommitConsistency ==
    \A k \in KEYS :
        \/ (lockTs[k] = 0 /\ commitTs[k] = 0)
        \/ commitTs[k] = 0
        \/ commitTs[k] > lockTs[k]

StrictCommitConsistency ==
    \A k \in KEYS :
        keyState[k] = "committed" => commitTs[k] > lockTs[k]

ResolvedTsConsistency ==
    \A i \in 1..Len(output) :
        i > resolvedPos => output[i] > resolvedTs

\* Liveness property

Progress ==
    ((\A k \in KEYS : pending[k] = 0) /\ fetched) ~> (resolvedTs > 0)

=============================================================================