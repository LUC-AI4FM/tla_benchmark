---------------------------- MODULE PCR ----------------------------
(***************************************************************************)
(* A very abstract model of the Polymerase Chain Reaction (PCR) cycle.    *)
(*                                                                         *)
(* State tracked:                                                          *)
(*   temp     - the current temperature of the reaction ("hot"/"cool")     *)
(*   primer   - number of free primers                                     *)
(*   dna      - number of double-stranded DNA molecules                    *)
(*   template - number of free single-stranded templates                   *)
(*   hybrid   - number of template-primer hybrids                          *)
(*                                                                         *)
(* The actions are:                                                        *)
(*   Heat   : denatures double-stranded DNA into two single-stranded       *)
(*            templates and separates hybrids into a template plus a       *)
(*            primer.                                                      *)
(*   Cool   : lowers the temperature so annealing / extension can occur.   *)
(*   Anneal : nondeterministically binds some number k of available        *)
(*            primers to the same number of available templates, forming   *)
(*            hybrids.                                                     *)
(*   Extend : converts every hybrid into a double-stranded DNA molecule.   *)
(*                                                                         *)
(* Many biochemical details (nucleotides, polymerase, strand direction,    *)
(* exact temperatures, timing, efficiency, etc.) are intentionally         *)
(* omitted; PCR is treated as a coarse state-transition system.            *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    InitPrimers,   \* initial number of free primers
    InitDNA        \* initial number of double-stranded DNA molecules

ASSUME /\ InitPrimers \in Nat
       /\ InitDNA \in Nat

VARIABLES temp, primer, dna, template, hybrid

vars == <<temp, primer, dna, template, hybrid>>

Temps == {"hot", "cool"}

Min(a, b) == IF a <= b THEN a ELSE b

\* Count-preservation quantity: each primer counts 1, each free template
\* counts 1, each hybrid (template + primer) counts 2, and each double-
\* stranded DNA molecule (two strands) counts 2.
Total == primer + template + 2 * hybrid + 2 * dna

InitTotal == InitPrimers + 2 * InitDNA

---------------------------------------------------------------------------

Init ==
    /\ temp = "cool"
    /\ primer = InitPrimers
    /\ dna = InitDNA
    /\ template = 0
    /\ hybrid = 0

\* Heating denatures DNA into single-stranded templates and separates
\* hybrids back into templates and primers.
Heat ==
    /\ temp = "cool"
    /\ temp' = "hot"
    /\ template' = template + hybrid + 2 * dna
    /\ primer' = primer + hybrid
    /\ dna' = 0
    /\ hybrid' = 0

\* Cooling the reaction.
Cool ==
    /\ temp = "hot"
    /\ temp' = "cool"
    /\ UNCHANGED <<primer, dna, template, hybrid>>

\* Annealing nondeterministically consumes some number k of available
\* primers and templates, producing k hybrids.
Anneal ==
    /\ temp = "cool"
    /\ \E k \in 1..Min(primer, template) :
          /\ primer' = primer - k
          /\ template' = template - k
          /\ hybrid' = hybrid + k
    /\ UNCHANGED <<temp, dna>>

\* Extension converts all hybrids into double-stranded DNA.
Extend ==
    /\ temp = "cool"
    /\ hybrid > 0
    /\ dna' = dna + hybrid
    /\ hybrid' = 0
    /\ UNCHANGED <<temp, primer, template>>

Next ==
    \/ Heat
    \/ Cool
    \/ Anneal
    \/ Extend

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

---------------------------------------------------------------------------
(* Safety properties                                                       *)
---------------------------------------------------------------------------

TypeOK ==
    /\ temp \in Temps
    /\ primer \in Nat
    /\ dna \in Nat
    /\ template \in Nat
    /\ hybrid \in Nat

NonNegative ==
    /\ primer >= 0
    /\ dna >= 0
    /\ template >= 0
    /\ hybrid >= 0

\* The weighted count of strands/primers is preserved by every action.
CountPreserved == Total = InitTotal

---------------------------------------------------------------------------
(* Liveness property                                                       *)
---------------------------------------------------------------------------

\* Claim: primers are eventually depleted.
\* NOTE: This property does NOT hold. Weak fairness on Next only ensures
\* that some step keeps happening; the system may forever alternate
\* Heat and Cool (or Heat, Cool, Extend) without ever annealing, or anneal
\* only some primers and then heat them free again, so primer need never
\* reach 0. TLC will report a counterexample (a lasso) for this property.
PrimerDepletion == <>(primer = 0)

THEOREM Spec => [](TypeOK /\ NonNegative /\ CountPreserved)

=============================================================================