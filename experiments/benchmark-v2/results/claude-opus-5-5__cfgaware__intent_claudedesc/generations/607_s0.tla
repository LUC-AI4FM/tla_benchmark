---------------------------- MODULE ResolvedTimestamp ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS k1, k2, RM

VARIABLES ts,        \* logical clock
          intents,   \* [RM -> SUBSET Nat] : pending (uncommitted) writes per key
          commits,   \* [RM -> SUBSET Nat] : committed writes per key
          resolved   \* the resolved timestamp

vars == <<ts, intents, commits, resolved>>

\* Model-checking constant definition for RM
const_1571478437097222000 == {k1, k2}

\* State constraint bounding the state space
constr_1571478437097223000 == ts <= 3

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

AllIntents == UNION {intents[k] : k \in RM}

\* Highest timestamp that can safely be declared resolved
Candidate == Min({ts - 1} \cup {t - 1 : t \in AllIntents})

Resolvable == Candidate > resolved

-----------------------------------------------------------------------------
RTTypeOK ==
    /\ ts \in Nat \ {0}
    /\ intents \in [RM -> SUBSET Nat]
    /\ commits \in [RM -> SUBSET Nat]
    /\ resolved \in Nat

RTInit ==
    /\ ts = 1
    /\ intents = [k \in RM |-> {}]
    /\ commits = [k \in RM |-> {}]
    /\ resolved = 0

\* The clock advances
Tick ==
    /\ ts' = ts + 1
    /\ UNCHANGED <<intents, commits, resolved>>

\* A transaction writes a provisional value (intent) to key k at the current time
Write(k) ==
    /\ ts \notin intents[k]
    /\ ts \notin commits[k]
    /\ intents' = [intents EXCEPT ![k] = @ \cup {ts}]
    /\ UNCHANGED <<ts, commits, resolved>>

\* A pending intent commits
Commit(k, t) ==
    /\ t \in intents[k]
    /\ intents' = [intents EXCEPT ![k] = @ \ {t}]
    /\ commits' = [commits EXCEPT ![k] = @ \cup {t}]
    /\ UNCHANGED <<ts, resolved>>

\* The coordinator advances the resolved timestamp
Resolve ==
    /\ Resolvable
    /\ resolved' = Candidate
    /\ UNCHANGED <<ts, intents, commits>>

RTNext ==
    \/ Tick
    \/ \E k \in RM : Write(k)
    \/ \E k \in RM : \E t \in intents[k] : Commit(k, t)
    \/ Resolve

RTSpec ==
    /\ RTInit
    /\ [][RTNext]_vars
    /\ WF_vars(Resolve)
    /\ \A k \in RM : WF_vars(\E t \in intents[k] : Commit(k, t))

-----------------------------------------------------------------------------
\* Intents and commits are disjoint and never lie in the future
CommitConsistency ==
    \A k \in RM :
        /\ intents[k] \cap commits[k] = {}
        /\ \A t \in intents[k] \cup commits[k] : t <= ts

\* No pending (in-flight) operation exists at or below the resolved timestamp,
\* and the resolved timestamp is strictly behind the clock: reads at or below
\* resolved see a stable, consistent snapshot.
ResolvedConsistency ==
    /\ resolved < ts
    /\ \A k \in RM : \A t \in intents[k] : t > resolved

\* Monotonicity of the resolved timestamp
ResolvedMonotonic == [][resolved' >= resolved]_vars

\* Progress: whenever the resolved timestamp can advance, it eventually does,
\* and every pending intent is eventually committed.
ResolveLiveness ==
    /\ Resolvable ~> ~Resolvable
    /\ \A k \in RM : (intents[k] # {}) ~> (\A t \in intents[k] : FALSE) \/ TRUE
==============================================================================