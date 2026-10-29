---------------------------- MODULE ResolvedTS ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT RM            \* the set of keys (resources) in the region

\* Internal bound on the timestamp oracle so that model checking stays finite.
MaxTS == 2 * Cardinality(RM) + 2

VARIABLES
    tso,          \* timestamp oracle: last timestamp handed out
    rmState,      \* lifecycle state of each key
    prewriteTS,   \* prewrite (lock) timestamp of each key, 0 if none
    commitTS,     \* commit timestamp of each key, 0 if none
    applied,      \* whether the resolver has applied the key's prewrite
    msgs,         \* ordered channel of messages to the resolver
    lockTS,       \* resolver's view of pending lock timestamps (0 = no lock)
    resolvedTS,   \* last computed resolved timestamp
    resolvedPos,  \* length of output queue when resolvedTS was computed
    output        \* output queue of commit timestamps

vars == << tso, rmState, prewriteTS, commitTS, applied, msgs,
           lockTS, resolvedTS, resolvedPos, output >>

TS == 0..MaxTS

PrewriteMsgs == [type : {"prewrite"}, key : RM, ts : TS]
CommitMsgs   == [type : {"commit"},   key : RM, ts : TS]
RollbackMsgs == [type : {"rollback"}, key : RM]
FetchMsgs    == [type : {"fetch"},    ts : TS]
Messages     == PrewriteMsgs \cup CommitMsgs \cup RollbackMsgs \cup FetchMsgs

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

RTTypeOK ==
    /\ tso \in TS
    /\ rmState \in [RM -> {"init", "prewrote", "committed", "rolledback"}]
    /\ prewriteTS \in [RM -> TS]
    /\ commitTS \in [RM -> TS]
    /\ applied \in [RM -> BOOLEAN]
    /\ msgs \in Seq(Messages)
    /\ lockTS \in [RM -> TS]
    /\ resolvedTS \in TS
    /\ resolvedPos \in Nat
    /\ output \in Seq(TS)

RTInit ==
    /\ tso = 0
    /\ rmState = [k \in RM |-> "init"]
    /\ prewriteTS = [k \in RM |-> 0]
    /\ commitTS = [k \in RM |-> 0]
    /\ applied = [k \in RM |-> FALSE]
    /\ msgs = << >>
    /\ lockTS = [k \in RM |-> 0]
    /\ resolvedTS = 0
    /\ resolvedPos = 0
    /\ output = << >>

\* Optimistic prewrite: timestamp freshly obtained from the oracle.
OptimisticPrewrite(k) ==
    /\ rmState[k] = "init"
    /\ tso < MaxTS
    /\ tso' = tso + 1
    /\ rmState' = [rmState EXCEPT ![k] = "prewrote"]
    /\ prewriteTS' = [prewriteTS EXCEPT ![k] = tso + 1]
    /\ msgs' = Append(msgs, [type |-> "prewrite", key |-> k, ts |-> tso + 1])
    /\ UNCHANGED << commitTS, applied, lockTS, resolvedTS, resolvedPos, output >>

\* Pessimistic prewrite: timestamp may be stale (obtained earlier).
PessimisticPrewrite(k) ==
    /\ rmState[k] = "init"
    /\ tso > 0
    /\ \E t \in 1..tso :
         /\ rmState' = [rmState EXCEPT ![k] = "prewrote"]
         /\ prewriteTS' = [prewriteTS EXCEPT ![k] = t]
         /\ msgs' = Append(msgs, [type |-> "prewrite", key |-> k, ts |-> t])
    /\ UNCHANGED << tso, commitTS, applied, lockTS, resolvedTS, resolvedPos, output >>

\* Commit only after the prewrite has been applied by the resolver.
Commit(k) ==
    /\ rmState[k] = "prewrote"
    /\ applied[k]
    /\ tso < MaxTS
    /\ tso' = tso + 1
    /\ rmState' = [rmState EXCEPT ![k] = "committed"]
    /\ commitTS' = [commitTS EXCEPT ![k] = tso + 1]
    /\ msgs' = Append(msgs, [type |-> "commit", key |-> k, ts |-> tso + 1])
    /\ UNCHANGED << prewriteTS, applied, lockTS, resolvedTS, resolvedPos, output >>

Rollback(k) ==
    /\ rmState[k] = "prewrote"
    /\ rmState' = [rmState EXCEPT ![k] = "rolledback"]
    /\ msgs' = Append(msgs, [type |-> "rollback", key |-> k])
    /\ UNCHANGED << tso, prewriteTS, commitTS, applied, lockTS,
                    resolvedTS, resolvedPos, output >>

\* Fetch a timestamp from the oracle and send it to the resolver.
FetchTS ==
    /\ tso < MaxTS
    /\ tso' = tso + 1
    /\ msgs' = Append(msgs, [type |-> "fetch", ts |-> tso + 1])
    /\ UNCHANGED << rmState, prewriteTS, commitTS, applied, lockTS,
                    resolvedTS, resolvedPos, output >>

\* The resolver processes the head of the channel.
Process ==
    /\ msgs # << >>
    /\ LET m == Head(msgs) IN
       /\ msgs' = Tail(msgs)
       /\ CASE m.type = "prewrite" ->
                 /\ lockTS' = [lockTS EXCEPT ![m.key] = m.ts]
                 /\ applied' = [applied EXCEPT ![m.key] = TRUE]
                 /\ UNCHANGED << resolvedTS, resolvedPos, output >>
            [] m.type = "commit" ->
                 /\ lockTS' = [lockTS EXCEPT ![m.key] = 0]
                 /\ output' = Append(output, m.ts)
                 /\ UNCHANGED << applied, resolvedTS, resolvedPos >>
            [] m.type = "rollback" ->
                 /\ lockTS' = [lockTS EXCEPT ![m.key] = 0]
                 /\ UNCHANGED << applied, resolvedTS, resolvedPos, output >>
            [] m.type = "fetch" ->
                 LET locks == { lockTS[k] : k \in { j \in RM : lockTS[j] > 0 } }
                 IN /\ resolvedTS' = Min(locks \cup {m.ts})
                    /\ resolvedPos' = Len(output)
                    /\ UNCHANGED << lockTS, applied, output >>
    /\ UNCHANGED << tso, rmState, prewriteTS, commitTS >>

Terminating ==
    /\ \A k \in RM : rmState[k] \in {"committed", "rolledback"}
    /\ msgs = << >>
    /\ UNCHANGED vars

RTNext ==
    \/ \E k \in RM : OptimisticPrewrite(k) \/ PessimisticPrewrite(k)
                     \/ Commit(k) \/ Rollback(k)
    \/ FetchTS
    \/ Process
    \/ Terminating

RTSpec == RTInit /\ [][RTNext]_vars /\ WF_vars(Process)

-----------------------------------------------------------------------------
\* Correctness properties

CommitConsistency ==
    \A k \in RM :
        \/ (commitTS[k] = 0 /\ prewriteTS[k] = 0)
        \/ (rmState[k] # "committed")
        \/ commitTS[k] > prewriteTS[k]

ResolvedConsistency ==
    \A i \in 1..Len(output) :
        i > resolvedPos => output[i] > resolvedTS

ResolveLiveness ==
    ( /\ \A k \in RM : rmState[k] \in {"committed", "rolledback"}
      /\ \E i \in 1..Len(msgs) : msgs[i].type = "fetch" )
    ~> (resolvedTS > 0)

=============================================================================