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
(* hold (the system can cycle without depleting primers).                  *)
(*                                                                         *)
(* The model intentionally omits many biochemical details and treats PCR   *)
(* as a coarse state-transition system.                                    *)
(***************************************************************************)

EXTENDS Naturals

CONSTANTS
    InitPrimers,      \* Initial number of primers
    InitDNA,          \* Initial number of double-stranded DNA molecules
    MaxPrimers,       \* Upper bound for primer count (for model checking)
    MaxDNA            \* Upper bound for DNA count (for model checking)

VARIABLES
    temperature,      \* Current temperature state: "high", "low", or "annealing"
    primers,          \* Count of available primers
    dna,              \* Count of double-stranded DNA molecules
    templates,        \* Count of single-stranded templates
    hybrids           \* Count of template-primer hybrids

vars == <<temperature, primers, dna, templates, hybrids>>

(***************************************************************************)
(* Type invariant: all counts are natural numbers and temperature is one   *)
(* of the valid states.                                                    *)
(***************************************************************************)
TypeOK ==
    /\ temperature \in {"high", "low", "annealing", "extension"}
    /\ primers \in Nat
    /\ dna \in Nat
    /\ templates \in Nat
    /\ hybrids \in Nat

(***************************************************************************)
(* Nonnegativity invariant: all counts remain non-negative.                *)
(* (This is implied by TypeOK but stated explicitly for clarity.)          *)
(***************************************************************************)
NonNegative ==
    /\ primers >= 0
    /\ dna >= 0
    /\ templates >= 0
    /\ hybrids >= 0

(***************************************************************************)
(* Count preservation invariant: the total genetic material is conserved.  *)
(* Each DNA contributes 2 strands, each template contributes 1, and each   *)
(* hybrid contributes 1 template strand (with a primer attached).          *)
(* The total strand count should remain constant.                          *)
(***************************************************************************)
TotalStrands == 2 * dna + templates + hybrids

CountPreservation ==
    TotalStrands = 2 * InitDNA

(***************************************************************************)
(* Initial state: start at low temperature with initial DNA, no templates  *)
(* or hybrids yet, and the initial primer count.                           *)
(***************************************************************************)
Init ==
    /\ temperature = "low"
    /\ primers = InitPrimers
    /\ dna = InitDNA
    /\ templates = 0
    /\ hybrids = 0

(***************************************************************************)
(* Heating action: raise temperature to denature DNA into single strands.  *)
(* Each double-stranded DNA molecule produces 2 single-stranded templates. *)
(***************************************************************************)
Heat ==
    /\ temperature = "low"
    /\ temperature' = "high"
    /\ templates' = templates + 2 * dna
    /\ dna' = 0
    /\ UNCHANGED <<primers, hybrids>>

(***************************************************************************)
(* Cooling action: lower temperature to prepare for annealing.             *)
(***************************************************************************)
Cool ==
    /\ temperature = "high"
    /\ temperature' = "annealing"
    /\ UNCHANGED <<primers, dna, templates, hybrids>>

(***************************************************************************)
(* Annealing action: primers bind to templates forming hybrids.            *)
(* Nondeterministically choose how many primers bind (0 to min of          *)
(* available primers and templates).                                       *)
(***************************************************************************)
Anneal ==
    /\ temperature = "annealing"
    /\ \E n \in 0..primers :
        /\ n <= templates
        /\ primers' = primers - n
        /\ templates' = templates - n
        /\ hybrids' = hybrids + n
        /\ temperature' = "extension"
        /\ UNCHANGED <<dna>>

(***************************************************************************)
(* Extension action: DNA polymerase extends primers on hybrids to form     *)
(* new double-stranded DNA. Each hybrid becomes a new DNA molecule.        *)
(* (Simplified: in reality, two hybrids would be needed for one complete   *)
(* dsDNA, but we abstract this detail.)                                    *)
(***************************************************************************)
Extend ==
    /\ temperature = "extension"
    /\ dna' = dna + hybrids
    /\ hybrids' = 0
    /\ temperature' = "low"
    /\ UNCHANGED <<primers, templates>>

(***************************************************************************)
(* Next-state relation: the system can heat, cool, anneal, or extend.      *)
(***************************************************************************)
Next ==
    \/ Heat
    \/ Cool
    \/ Anneal
    \/ Extend

(***************************************************************************)
(* Fairness: we require weak fairness on all actions to ensure progress.   *)
(***************************************************************************)
Fairness ==
    /\ WF_vars(Heat)
    /\ WF_vars(Cool)
    /\ WF_vars(Anneal)
    /\ WF_vars(Extend)

(***************************************************************************)
(* Complete specification with fairness.                                   *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Safety invariants.                                                      *)
(***************************************************************************)
Safety ==
    /\ TypeOK
    /\ NonNegative

(***************************************************************************)
(* Liveness property: eventually all primers are depleted.                 *)
(* NOTE: This property does NOT hold! The annealing step can               *)
(* nondeterministically choose n=0, meaning no primers are consumed,       *)
(* allowing the system to cycle indefinitely without depleting primers.    *)
(***************************************************************************)
EventualPrimerDepletion == <>(primers = 0)

=============================================================================