---------------------------- MODULE PCR ----------------------------
(***************************************************************************)
(* An abstract model of the polymerase chain reaction (PCR).              *)
(*                                                                         *)
(* Species tracked (counts of molecules):                                  *)
(*   dna      - intact double-stranded target molecules (2 strands each)   *)
(*   template - free single-stranded templates (1 strand each)             *)
(*   primer   - free primer molecules (pooled count, 1 unit each)          *)
(*   hybrid   - primer-template hybrids (template + primer = 2 units)      *)
(*                                                                         *)
(* Temperature cycles through three phases:                                *)
(*   "denature" (high) -> "anneal" (low) -> "extend" (intermediate)        *)
(*   -> "denature" ...                                                     *)
(*                                                                         *)
(* Conserved quantity (strand/primer material):                            *)
(*   primer + template + 2*hybrid + 2*dna = PRIMER + 2*DNA                 *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS DNA,     \* initial number of double-stranded target molecules
          PRIMER   \* initial number of primer molecules

ASSUME DNA \in Nat /\ PRIMER \in Nat

VARIABLES temperature, dna, template, primer, hybrid

vars == <<temperature, dna, template, primer, hybrid>>

Phases == {"denature", "anneal", "extend"}

Min(a, b) == IF a <= b THEN a ELSE b

TotalMaterial == PRIMER + 2 * DNA

-----------------------------------------------------------------------------
TypeOK ==
    /\ temperature \in Phases
    /\ dna \in Nat
    /\ template \in Nat
    /\ primer \in Nat
    /\ hybrid \in Nat

primerPositive == primer >= 0

NonNegative ==
    /\ dna >= 0
    /\ template >= 0
    /\ primer >= 0
    /\ hybrid >= 0

preservationInvariant ==
    primer + template + 2 * hybrid + 2 * dna = TotalMaterial

-----------------------------------------------------------------------------
Init ==
    /\ temperature = "extend"
    /\ dna = DNA
    /\ template = 0
    /\ primer = PRIMER
    /\ hybrid = 0

(* Heat to high temperature: double strands melt into two single strands; *)
(* hybrids dissociate into a template and a free primer.                  *)
Denature ==
    /\ temperature = "extend"
    /\ temperature' = "denature"
    /\ template' = template + 2 * dna + hybrid
    /\ primer' = primer + hybrid
    /\ dna' = 0
    /\ hybrid' = 0

(* Cool to the annealing temperature. *)
Cool ==
    /\ temperature = "denature"
    /\ temperature' = "anneal"
    /\ UNCHANGED <<dna, template, primer, hybrid>>

(* Annealing: a nondeterministic number k of primers bind to templates,   *)
(* bounded by availability of both.                                       *)
Anneal ==
    /\ temperature = "anneal"
    /\ \E k \in 1..Min(primer, template) :
          /\ primer' = primer - k
          /\ template' = template - k
          /\ hybrid' = hybrid + k
    /\ UNCHANGED <<temperature, dna>>

(* Warm to the intermediate extension temperature. *)
Warm ==
    /\ temperature = "anneal"
    /\ temperature' = "extend"
    /\ UNCHANGED <<dna, template, primer, hybrid>>

(* Extension: polymerase extends primers on hybrids, yielding new double  *)
(* strands (nucleotides are drawn from an untracked reservoir).           *)
Extend ==
    /\ temperature = "extend"
    /\ hybrid > 0
    /\ dna' = dna + hybrid
    /\ hybrid' = 0
    /\ UNCHANGED <<temperature, template, primer>>

Next == Denature \/ Cool \/ Anneal \/ Warm \/ Extend

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)
    /\ WF_vars(Denature)
    /\ WF_vars(Cool)
    /\ WF_vars(Warm)

-----------------------------------------------------------------------------
(* Safety *)
preservationProperty == [](preservationInvariant /\ NonNegative)

(* Liveness: the system cycles forever. *)
CyclesForever == []<>(temperature = "denature")

(* The system *can* amplify; checked as a negated invariant witness:      *)
(* violation of NoAmplification exhibits extra double-stranded product.   *)
NoAmplification == dna <= DNA

(* Primer depletion witness: violation shows primers can be exhausted.    *)
PrimersNeverDepleted == primer > 0

(* Once primers are depleted (outside denaturation), no more annealing.   *)
DepletionConsequence ==
    [][(primer = 0 /\ temperature = "anneal") => hybrid' = hybrid]_vars

=============================================================================