------------------------------ MODULE ReactionPipeline ------------------------------
(***************************************************************************)
(* A biochemical sample-processing pipeline.  One processing station       *)
(* alternates between two atomic steps:                                    *)
(*   - Assemble: choose an available template, primer and DNA item, bind   *)
(*     them into a hybrid complex, and produce a reaction outcome.         *)
(*   - Cleanup: for every bound reagent, either restore it to available or *)
(*     consume it permanently, according to a nondeterministic policy.     *)
(* Because one station alternates, assemblies never overlap with each      *)
(* other, and cleanups never overlap with each other.  When no complete    *)
(* reagent triple is available, the station terminates.                    *)
(***************************************************************************)
EXTENDS FiniteSets

CONSTANTS
    Templates,    \* finite set of template items
    Primers,      \* finite set of primer items
    DNAs,         \* finite set of DNA items
    Outcomes      \* possible reaction outcomes (for example success or failure)

ASSUME
    /\ IsFiniteSet(Templates) /\ IsFiniteSet(Primers) /\ IsFiniteSet(DNAs)
    /\ Templates \cap Primers = {}
    /\ Templates \cap DNAs = {}
    /\ Primers \cap DNAs = {}
    /\ Outcomes /= {}

Reagents == Templates \cup Primers \cup DNAs

Phases == {"assemble", "cleanup", "done"}

\* Policies that the cleanup step may choose from.
Policies == {"restore", "consume", "mixed"}

(* A hybrid complex records its components, a snapshot of the reagents    *)
(* that were available when it was created, and the reaction outcome.     *)
HybridRecs ==
    [tmpl : Templates, prim : Primers, dna : DNAs,
     snap : SUBSET Reagents, outcome : Outcomes]

VARIABLES
    avail,      \* reagents currently available
    bound,      \* reagents currently bound in the active hybrid
    consumed,   \* reagents permanently consumed
    phase,      \* station phase: "assemble", "cleanup" or "done"
    current,    \* the active hybrid ({} or a singleton set)
    hybrids,    \* history of all hybrids that have been formed
    policy      \* the most recently applied cleanup policy

vars == <<avail, bound, consumed, phase, current, hybrids, policy>>

-----------------------------------------------------------------------------
(* Helper definitions *)

AvailCount(S)    == Cardinality(avail \cap S)
BoundCount(S)    == Cardinality(bound \cap S)
ConsumedCount(S) == Cardinality(consumed \cap S)

CanAssemble ==
    /\ avail \cap Templates /= {}
    /\ avail \cap Primers /= {}
    /\ avail \cap DNAs /= {}

HybridFormed == current /= {}

AllConsumed == consumed = Reagents

Terminated == phase = "done"

-----------------------------------------------------------------------------
TypeOK ==
    /\ avail \subseteq Reagents
    /\ bound \subseteq Reagents
    /\ consumed \subseteq Reagents
    /\ phase \in Phases
    /\ current \subseteq HybridRecs /\ Cardinality(current) <= 1
    /\ hybrids \subseteq HybridRecs
    /\ policy \in Policies \cup {"none"}

Init ==
    /\ avail = Reagents
    /\ bound = {}
    /\ consumed = {}
    /\ phase = "assemble"
    /\ current = {}
    /\ hybrids = {}
    /\ policy = "none"

(* Atomic assembly: nondeterministically select one available template,  *)
(* primer and DNA item, bind them, and produce an outcome.                *)
Assemble ==
    /\ phase = "assemble"
    /\ \E t \in avail \cap Templates, p \in avail \cap Primers,
          d \in avail \cap DNAs, o \in Outcomes :
        LET h == [tmpl |-> t, prim |-> p, dna |-> d,
                  snap |-> avail, outcome |-> o]
        IN  /\ avail'   = avail \ {t, p, d}
            /\ bound'   = bound \cup {t, p, d}
            /\ current' = {h}
            /\ hybrids' = hybrids \cup {h}
    /\ phase' = "cleanup"
    /\ UNCHANGED <<consumed, policy>>

(* Atomic cleanup: each bound reagent is restored or consumed.            *)
(*   "restore" restores all bound reagents,                               *)
(*   "consume" consumes all bound reagents, and                           *)
(*   "mixed" restores some bound reagents and consumes the rest.          *)
Cleanup ==
    /\ phase = "cleanup"
    /\ \E pol \in Policies, keep \in SUBSET bound :
        /\ (pol = "restore") => (keep = bound)
        /\ (pol = "consume") => (keep = {})
        /\ avail'    = avail \cup keep
        /\ consumed' = consumed \cup (bound \ keep)
        /\ policy'   = pol
    /\ bound'   = {}
    /\ current' = {}
    /\ phase'   = "assemble"
    /\ UNCHANGED hybrids

(* Termination: no complete triple of reagents is available.              *)
Terminate ==
    /\ phase = "assemble"
    /\ ~CanAssemble
    /\ phase' = "done"
    /\ UNCHANGED <<avail, bound, consumed, current, hybrids, policy>>

(* Once terminated, the system stutters.  This is intended termination,   *)
(* not deadlock.                                                          *)
Halted ==
    /\ phase = "done"
    /\ UNCHANGED vars

Next == Assemble \/ Cleanup \/ Terminate \/ Halted

Fairness ==
    /\ WF_vars(Assemble)
    /\ WF_vars(Cleanup)
    /\ WF_vars(Terminate)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety invariants *)

\* Reagent counts are never negative.
NonNegativeCounts ==
    \A S \in {Templates, Primers, DNAs} :
        /\ AvailCount(S) >= 0
        /\ BoundCount(S) >= 0
        /\ ConsumedCount(S) >= 0

\* No reagent is both available and consumed.
NotAvailableAndConsumed == avail \cap consumed = {}

\* Every reagent is in exactly one state.
Partition ==
    /\ avail \cup bound \cup consumed = Reagents
    /\ avail \cap bound = {}
    /\ bound \cap consumed = {}
    /\ avail \cap consumed = {}

\* Each hybrid references only reagents that were available at creation.
HybridsWellFormed ==
    \A h \in hybrids : {h.tmpl, h.prim, h.dna} \subseteq h.snap

\* The active hybrid's components are exactly the bound reagents.
CurrentConsistent ==
    /\ (phase = "cleanup") <=> HybridFormed
    /\ \A h \in current : bound = {h.tmpl, h.prim, h.dna}
    /\ (current = {}) => (bound = {})

\* Assembly and cleanup never overlap.  There is at most one active hybrid.
NoOverlap == Cardinality(current) <= 1

\* Freedom from deadlock: until termination, some step is always enabled.
NoDeadlock ==
    ~Terminated => ENABLED (Assemble \/ Cleanup \/ Terminate)

\* The system terminates only when reagents are exhausted.
TerminationCondition ==
    Terminated => (~CanAssemble /\ bound = {} /\ current = {})

\* If all reagents are consumed, nothing can be assembled.
ConsumedImpliesExhausted == AllConsumed => ~CanAssemble

Invariants ==
    /\ TypeOK
    /\ NonNegativeCounts
    /\ NotAvailableAndConsumed
    /\ Partition
    /\ HybridsWellFormed
    /\ CurrentConsistent
    /\ NoOverlap
    /\ NoDeadlock
    /\ TerminationCondition
    /\ ConsumedImpliesExhausted

-----------------------------------------------------------------------------
(* Liveness properties *)

\* When a template, primer and DNA item are available, eventually either a
\* hybrid forms or the reagents become unavailable.
AssemblyProgress == CanAssemble ~> (HybridFormed \/ ~CanAssemble)

\* The station keeps making progress: it is always eventually assembling
\* or cleaning, unless it has terminated.
Progress == []<>(HybridFormed \/ phase = "assemble" \/ Terminated)

\* Every active hybrid is eventually cleaned up.
CleanupEventually == HybridFormed ~> ~HybridFormed

\* When all reagents are consumed, the system eventually terminates.
TerminationOnConsumption == AllConsumed ~> Terminated

\* Exhausted reagents at the assembly phase lead to termination.
TerminationOnExhaustion == (phase = "assemble" /\ ~CanAssemble) ~> Terminated

\* Once terminated, the system stays terminated.
TerminationStable == [](Terminated => []Terminated)

=============================================================================