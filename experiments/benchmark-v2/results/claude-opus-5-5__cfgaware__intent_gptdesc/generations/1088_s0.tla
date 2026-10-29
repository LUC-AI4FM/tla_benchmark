---------------------------- MODULE SamplePipeline ----------------------------
EXTENDS Naturals

CONSTANTS DNA, PRIMER

ASSUME DNA \in Nat /\ PRIMER \in Nat

VARIABLES stage, template, primer, dna, hybrid

vars == <<stage, template, primer, dna, hybrid>>

Min(a, b) == IF a <= b THEN a ELSE b

Stages == {"assemble", "cleanup", "done"}

-----------------------------------------------------------------------------
Init ==
    /\ stage    = "assemble"
    /\ template = 0
    /\ primer   = PRIMER
    /\ dna      = DNA
    /\ hybrid   = 0

-----------------------------------------------------------------------------
(* Assembly: annealing binds k templates with k primers into k hybrids.     *)
Anneal(k) ==
    /\ stage = "assemble"
    /\ k \in 1..Min(template, primer)
    /\ template' = template - k
    /\ primer'   = primer - k
    /\ hybrid'   = hybrid + k
    /\ stage'    = "cleanup"
    /\ UNCHANGED dna

(* Assembly: denaturing k DNA molecules releases 2k template strands.       *)
Denature(k) ==
    /\ stage = "assemble"
    /\ k \in 1..dna
    /\ dna'      = dna - k
    /\ template' = template + 2 * k
    /\ stage'    = "cleanup"
    /\ UNCHANGED <<primer, hybrid>>

AssemblyPossible ==
    \/ (template > 0 /\ primer > 0)
    \/ dna > 0

(* No assembly possible, but hybrids remain to be cleaned up.               *)
SkipAssemble ==
    /\ stage = "assemble"
    /\ ~AssemblyPossible
    /\ hybrid > 0
    /\ stage' = "cleanup"
    /\ UNCHANGED <<template, primer, dna, hybrid>>

(* Cleanup policy 1: permanently consume primers by extending hybrids.      *)
Extend(k) ==
    /\ stage = "cleanup"
    /\ k \in 1..hybrid
    /\ hybrid' = hybrid - k
    /\ dna'    = dna + k
    /\ stage'  = "assemble"
    /\ UNCHANGED <<template, primer>>

(* Cleanup policy 2: restore reagents by dissociating hybrids.              *)
Restore(k) ==
    /\ stage = "cleanup"
    /\ k \in 1..hybrid
    /\ hybrid'   = hybrid - k
    /\ template' = template + k
    /\ primer'   = primer + k
    /\ stage'    = "assemble"
    /\ UNCHANGED dna

(* Cleanup policy 3: reset the station without touching reagents.           *)
Reset ==
    /\ stage = "cleanup"
    /\ stage' = "assemble"
    /\ UNCHANGED <<template, primer, dna, hybrid>>

-----------------------------------------------------------------------------
(* Termination: reagents exhausted.                                         *)
Exhausted ==
    /\ ~AssemblyPossible
    /\ hybrid = 0

Terminate ==
    /\ stage = "assemble"
    /\ Exhausted
    /\ stage' = "done"
    /\ UNCHANGED <<template, primer, dna, hybrid>>

Terminated ==
    /\ stage = "done"
    /\ UNCHANGED vars

AnnealStep  == \E k \in 1..(PRIMER + 2 * DNA) : Anneal(k)
DenatureStep == \E k \in 1..(PRIMER + 2 * DNA) : Denature(k)
ExtendStep  == \E k \in 1..(PRIMER + 2 * DNA) : Extend(k)
RestoreStep == \E k \in 1..(PRIMER + 2 * DNA) : Restore(k)

Next ==
    \/ AnnealStep
    \/ DenatureStep
    \/ SkipAssemble
    \/ ExtendStep
    \/ RestoreStep
    \/ Reset
    \/ Terminate
    \/ Terminated

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)
    /\ SF_vars(AnnealStep)

-----------------------------------------------------------------------------
(* Invariants                                                               *)

TypeOK ==
    /\ stage    \in Stages
    /\ template \in Nat
    /\ primer   \in Nat
    /\ dna      \in Nat
    /\ hybrid   \in Nat

primerPositive == primer >= 0

NonNegative ==
    /\ template >= 0
    /\ primer   >= 0
    /\ dna      >= 0
    /\ hybrid   >= 0

(* Mass balance: every unit in a hybrid or DNA came from available reagents *)
preservationInvariant ==
    template + primer + 2 * (dna + hybrid) = PRIMER + 2 * DNA

(* Primers are either available, bound in hybrids, or consumed into DNA;   *)
(* the consumed count is the remainder and is never negative, so no primer *)
(* is counted as both available and consumed.                              *)
ConsumedPrimers == PRIMER - (primer + hybrid)

NoDoubleMark ==
    /\ primer + hybrid <= PRIMER + 2 * DNA
    /\ hybrid <= PRIMER + 2 * DNA

HybridFromAvailable ==
    hybrid <= PRIMER + DNA * 2 - (template + primer + 2 * dna) 

-----------------------------------------------------------------------------
(* Liveness                                                                 *)

HybridProgress ==
    ((stage = "assemble") /\ template > 0 /\ primer > 0)
        ~> (hybrid > 0 \/ template = 0 \/ primer = 0)

EventuallyProgressOrDone ==
    []<>(stage # "done" \/ Exhausted)

TerminationCondition ==
    (stage = "done") => Exhausted

=============================================================================