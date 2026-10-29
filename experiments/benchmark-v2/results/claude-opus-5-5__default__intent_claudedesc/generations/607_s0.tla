---------------------------- MODULE ResolvedTimestamp ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    Keys,      \* set of resource managers / key ranges (e.g. {k1, k2})
    MaxTs      \* bound on the logical clock for model checking

ASSUME MaxTs \in Nat /\ MaxTs >= 1
ASSUME Keys # {} /\ IsFiniteSet(Keys)

NoIntent == 0   \* timestamp 0 denotes "no pending operation"

VARIABLES
    clock,      \* logical clock / timestamp oracle
    intent,     \* intent[k] = timestamp of pending (uncommitted) write on k, or NoIntent
    committed,  \* set of committed writes [key |-> k, ts |-> t]
    resolved    \* the resolved timestamp

vars == <<clock, intent, committed, resolved>>

Timestamps == 0..MaxTs
WriteRecs  == [key : Keys, ts : 1..MaxTs]

TypeOK ==
    /\ clock \in Timestamps
    /\ intent \in [Keys -> Timestamps]
    /\ committed \subseteq WriteRecs
    /\ resolved \in Timestamps

-----------------------------------------------------------------------------
\* Helpers

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

PendingTs == { intent[k] : k \in { kk \in Keys : intent[kk] # NoIntent } }

\* Highest timestamp below every in-flight operation, bounded by the clock.
CandidateResolved ==
    IF PendingTs = {} THEN clock
    ELSE IF Min(PendingTs) - 1 < clock THEN Min(PendingTs) - 1 ELSE clock

\* A snapshot read at timestamp t sees all committed writes with ts <= t.
Snapshot(t) == { w \in committed : w.ts <= t }

-----------------------------------------------------------------------------
Init ==
    /\ clock = 0
    /\ intent = [k \in Keys |-> NoIntent]
    /\ committed = {}
    /\ resolved = 0

\* The logical clock advances.
Tick ==
    /\ clock < MaxTs
    /\ clock' = clock + 1
    /\ UNCHANGED <<intent, committed, resolved>>

\* A resource manager begins a write at the current clock. Writes are
\* only admitted strictly above the resolved timestamp.
BeginWrite(k) ==
    /\ intent[k] = NoIntent
    /\ clock > resolved
    /\ intent' = [intent EXCEPT ![k] = clock]
    /\ UNCHANGED <<clock, committed, resolved>>

\* The pending write on k commits.
Commit(k) ==
    /\ intent[k] # NoIntent
    /\ committed' = committed \cup { [key |-> k, ts |-> intent[k]] }
    /\ intent' = [intent EXCEPT ![k] = NoIntent]
    /\ UNCHANGED <<clock, resolved>>

\* The pending write on k aborts.
Abort(k) ==
    /\ intent[k] # NoIntent
    /\ intent' = [intent EXCEPT ![k] = NoIntent]
    /\ UNCHANGED <<clock, committed, resolved>>

Finish(k) == Commit(k) \/ Abort(k)

\* The coordinator advances the resolved timestamp.
AdvanceResolved ==
    /\ CandidateResolved > resolved
    /\ resolved' = CandidateResolved
    /\ UNCHANGED <<clock, intent, committed>>

Next ==
    \/ Tick
    \/ AdvanceResolved
    \/ \E k \in Keys : BeginWrite(k) \/ Finish(k)

Fairness ==
    /\ \A k \in Keys : WF_vars(Finish(k))
    /\ SF_vars(AdvanceResolved)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety invariants

\* The resolved timestamp never passes any in-flight operation.
ResolvedSafety ==
    \A k \in Keys : intent[k] # NoIntent => intent[k] > resolved

\* The resolved timestamp never exceeds the clock.
ResolvedBoundedByClock == resolved <= clock

\* All committed data is at or below the clock.
CommittedBoundedByClock == \A w \in committed : w.ts <= clock

SafetyInv ==
    /\ TypeOK
    /\ ResolvedSafety
    /\ ResolvedBoundedByClock
    /\ CommittedBoundedByClock

\* Monotonicity: the resolved timestamp never decreases.
Monotonicity == [][resolved' >= resolved]_vars

\* Safe reads: the snapshot at the resolved timestamp is stable; every
\* newly committed write lies strictly above the resolved timestamp.
SafeReads ==
    [][ /\ \A w \in committed' \ committed : w.ts > resolved
        /\ Snapshot(resolved)' \cap { w \in committed' : w.ts <= resolved }
             = Snapshot(resolved) ]_vars

-----------------------------------------------------------------------------
\* Liveness

\* Every pending operation eventually completes.
IntentsComplete ==
    \A k \in Keys : (intent[k] # NoIntent) ~> (intent[k] = NoIntent)

\* The resolved timestamp eventually catches up to any reached clock value.
Progress ==
    \A t \in Timestamps : (clock >= t) ~> (resolved >= t)

=============================================================================