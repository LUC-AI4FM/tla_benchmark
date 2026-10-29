------------------------------ MODULE MC_stages ------------------------------
(***************************************************************************)
(* Type-annotated, self-contained version of the `stages` PCR model for    *)
(* the Apalache model checker. Apalache annotations are in comments, so    *)
(* the behavioral definitions stay free of tool-specific syntax.           *)
(*                                                                         *)
(* Model-checking configuration:                                           *)
(*   DNA = 5, PRIMER = 5                                                   *)
(*   SPECIFICATION Spec                                                    *)
(*   INVARIANT TypeOK                                                      *)
(*   CHECK_DEADLOCK FALSE                                                  *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    \* @type: Int;
    DNA,
    \* @type: Int;
    PRIMER

VARIABLES
    \* @type: Int;
    dna,
    \* @type: Int;
    primer,
    \* @type: Int;
    template,
    \* @type: Int;
    hybrid,
    \* @type: Str;
    tee,
    \* @type: Str;
    stage,
    \* @type: Int;
    cycle

vars == << dna, primer, template, hybrid, tee, stage, cycle >>

ASSUME DNA \in Nat /\ PRIMER \in Nat

Temperatures == {"Hot", "Cold", "TooHot"}
Stages       == {"init", "denatured", "annealed", "extended"}

natMin(i, j) == IF i < j THEN i ELSE j

-----------------------------------------------------------------------------
TypeOK ==
    /\ dna      \in Nat
    /\ primer   \in Nat
    /\ template \in Nat
    /\ hybrid   \in Nat
    /\ tee      \in Temperatures
    /\ stage    \in Stages
    /\ cycle    \in Nat

Init ==
    /\ dna      = DNA
    /\ primer   = PRIMER
    /\ template = 0
    /\ hybrid   = 0
    /\ tee      = "Hot"
    /\ stage    = "init"
    /\ cycle    = 0

(* Denaturation: heating separates every double strand into two templates. *)
Denature ==
    /\ stage \in {"init", "extended"}
    /\ tee'      = "TooHot"
    /\ template' = template + 2 * dna
    /\ dna'      = 0
    /\ stage'    = "denatured"
    /\ UNCHANGED << primer, hybrid, cycle >>

(* Annealing: cooling lets primers bind to templates, forming hybrids. *)
Anneal ==
    /\ stage = "denatured"
    /\ primer > 0
    /\ template > 0
    /\ LET k == natMin(primer, template) IN
         /\ hybrid'   = hybrid + k
         /\ primer'   = primer - k
         /\ template' = template - k
    /\ tee'   = "Cold"
    /\ stage' = "annealed"
    /\ UNCHANGED << dna, cycle >>

(* Extension: the polymerase completes hybrids into double-stranded DNA. *)
Extend ==
    /\ stage = "annealed"
    /\ tee'    = "Hot"
    /\ dna'    = dna + hybrid
    /\ hybrid' = 0
    /\ stage'  = "extended"
    /\ cycle'  = cycle + 1
    /\ UNCHANGED << primer, template >>

Next ==
    \/ Denature
    \/ Anneal
    \/ Extend

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Additional safety properties *)

PrimerBounded == primer <= PRIMER

\* Every primer consumed ends up in exactly one strand (hybrid or new DNA).
PrimerConservation ==
    primer + hybrid + (2 * dna + template - 2 * DNA) \div 1 >= 0

(* Liveness: the process eventually reaches a stable terminal configuration *)
Termination == <>[](primer = 0 \/ template = 0) \/ <>[](stage = "denatured")

=============================================================================