-------------------------------- MODULE PCR --------------------------------
(***************************************************************************)
(* A very abstract model of the PCR (Polymerase Chain Reaction) cycle,     *)
(* tracking temperature and counts of primers, double-stranded DNA,        *)
(* single-stranded templates, and template-primer hybrids.                 *)
(*                                                                         *)
(* The system alternates among heating, cooling, annealing, and extension  *)
(* actions. Annealing nondeterministically consumes some number of         *)
(* available primers and templates, and extension converts hybrids into    *)
(* DNA.                                                                    *)
(*                                                                         *)
(* This specification checks basic safety-style properties such as typing, *)
(* nonnegativity, and a count-preservation invariant. It also states a     *)
(* liveness property claiming eventual primer depletion, which does NOT    *)
(* hold (included intentionally as noted in comments).                     *)
(*                                                                         *)
(* The model intentionally omits many biochemical details and treats PCR   *)
(* as a coarse state-transition system.                                    *)
(***************************************************************************)

EXTENDS Integers, Naturals

CONSTANTS InitPrimers,      \* Initial number of primers
          InitDNA,          \* Initial number of double-stranded DNA molecules
          MaxTemp,          \* Maximum (denaturing) temperature
          MinTemp           \* Minimum (annealing/extension) temperature

VARIABLES temp,             \* Current temperature (abstract: "high" or "low")
          primers,          \* Count of available primers
          dsDNA,            \* Count of double-stranded DNA
          ssDNA,            \* Count of single-stranded DNA templates
          hybrids,          \* Count of template-primer hybrids
          phase             \* Current phase: "heating", "cooling", "annealing", "extension"

vars == <<temp, primers, dsDNA, ssDNA, hybrids, phase>>

(***************************************************************************)
(* Type invariant                                                          *)
(***************************************************************************)
TypeOK ==
    /\ temp \in {MinTemp, MaxTemp}
    /\ primers \in Nat
    /\ dsDNA \in Nat
    /\ ssDNA \in Nat
    /\ hybrids \in Nat
    /\ phase \in {"heating", "cooling", "annealing", "extension"}

(***************************************************************************)
(* Nonnegativity invariant                                                 *)
(***************************************************************************)
Nonnegative ==
    /\ primers >= 0
    /\ dsDNA >= 0
    /\ ssDNA >= 0
    /\ hybrids >= 0

(***************************************************************************)
(* Count preservation invariant:                                           *)
(* The total "template units" are conserved. Each dsDNA contributes 2      *)
(* template strands, each ssDNA contributes 1, each hybrid contributes 1.  *)
(* Primers are consumed but tracked separately.                            *)
(***************************************************************************)
InitialTemplateUnits == 2 * InitDNA

CountPreservation ==
    2 * dsDNA + ssDNA + hybrids = InitialTemplateUnits

(***************************************************************************)
(* Initial state                                                           *)
(***************************************************************************)
Init ==
    /\ temp = MinTemp
    /\ primers = InitPrimers
    /\ dsDNA = InitDNA
    /\ ssDNA = 0
    /\ hybrids = 0
    /\ phase = "heating"

(***************************************************************************)
(* Heating action: Raise temperature to denature dsDNA into ssDNA          *)
(* Each dsDNA molecule separates into 2 single-stranded templates.         *)
(***************************************************************************)
Heat ==
    /\ phase = "heating"
    /\ temp' = MaxTemp
    /\ ssDNA' = ssDNA + 2 * dsDNA
    /\ dsDNA' = 0
    /\ primers' = primers
    /\ hybrids' = hybrids
    /\ phase' = "cooling"

(***************************************************************************)
(* Cooling action: Lower temperature to allow annealing                    *)
(***************************************************************************)
Cool ==
    /\ phase = "cooling"
    /\ temp' = MinTemp
    /\ primers' = primers
    /\ dsDNA' = dsDNA
    /\ ssDNA' = ssDNA
    /\ hybrids' = hybrids
    /\ phase' = "annealing"

(***************************************************************************)
(* Annealing action: Primers bind to single-stranded templates             *)
(* Nondeterministically choose how many primers anneal (0 to min of        *)
(* available primers and templates).                                       *)
(***************************************************************************)
Anneal ==
    /\ phase = "annealing"
    /\ temp = MinTemp
    /\ \E n \in 0..primers:
        /\ n <= ssDNA
        /\ primers' = primers - n
        /\ ssDNA' = ssDNA - n
        /\ hybrids' = hybrids + n
        /\ dsDNA' = dsDNA
        /\ temp' = temp
    /\ phase' = "extension"

(***************************************************************************)
(* Extension action: DNA polymerase extends primers to form new dsDNA      *)
(* Each hybrid becomes a complete double-stranded DNA molecule.            *)
(***************************************************************************)
Extend ==
    /\ phase = "extension"
    /\ temp = MinTemp
    /\ dsDNA' = dsDNA + hybrids
    /\ hybrids' = 0
    /\ primers' = primers
    /\ ssDNA' = ssDNA
    /\ temp' = temp
    /\ phase' = "heating"

(***************************************************************************)
(* Next state relation                                                     *)
(***************************************************************************)
Next ==
    \/ Heat
    \/ Cool
    \/ Anneal
    \/ Extend

(***************************************************************************)
(* Fairness: We require weak fairness on all actions to reason about       *)
(* liveness properties.                                                    *)
(***************************************************************************)
Fairness ==
    /\ WF_vars(Heat)
    /\ WF_vars(Cool)
    /\ WF_vars(Anneal)
    /\ WF_vars(Extend)

(***************************************************************************)
(* Complete specification with fairness                                    *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Safety invariants                                                       *)
(***************************************************************************)
Safety ==
    /\ TypeOK
    /\ Nonnegative
    /\ CountPreservation

(***************************************************************************)
(* Liveness property: Eventually all primers are depleted.                 *)
(* NOTE: This property does NOT hold! The annealing action can             *)
(* nondeterministically choose n=0, meaning primers may never be fully     *)
(* consumed. This is included intentionally to demonstrate a liveness      *)
(* property that fails.                                                    *)
(***************************************************************************)
EventualPrimerDepletion == <>(primers = 0)

=============================================================================