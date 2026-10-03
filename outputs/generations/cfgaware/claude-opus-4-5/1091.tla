-------------------------------- MODULE pcr --------------------------------

EXTENDS Integers, Naturals

CONSTANTS InitPrimers, InitDNA, InitTemplates, MaxConsume

VARIABLES temp, primers, dna, templates, hybrids, phase

vars == <<temp, primers, dna, templates, hybrids, phase>>

(* Type invariant: all counts are natural numbers, temp is a valid temperature state,
   and phase is one of the valid phases *)
TypeOK ==
    /\ temp \in {"hot", "cold", "warm"}
    /\ primers \in Nat
    /\ dna \in Nat
    /\ templates \in Nat
    /\ hybrids \in Nat
    /\ phase \in {"heating", "cooling", "annealing", "extension"}

(* Safety property: primers count is always non-negative *)
primerPositive == primers >= 0

(* Preservation invariant: total genetic material is conserved
   Each DNA contributes 2 strands, each template is 1 strand, each hybrid is 1 template + 1 primer bound
   Total strands = 2*dna + templates + hybrids should be preserved
   Also primers + hybrids should relate to initial primers *)
preservationInvariant ==
    /\ 2 * dna + templates + hybrids = 2 * InitDNA + InitTemplates
    /\ primers + hybrids = InitPrimers

(* Temporal preservation property - always maintains the invariant *)
preservationProperty == []preservationInvariant

(* Liveness property: eventually primers are depleted
   NOTE: This property does NOT hold in general because the system can
   stutter or cycle without consuming all primers *)
eventualPrimerDepletion == <>(primers = 0)

(* Initial state *)
Init ==
    /\ temp = "cold"
    /\ primers = InitPrimers
    /\ dna = InitDNA
    /\ templates = InitTemplates
    /\ hybrids = 0
    /\ phase = "heating"

(* Heating action: raises temperature to denature DNA into single strands *)
Heat ==
    /\ phase = "heating"
    /\ temp' = "hot"
    /\ templates' = templates + 2 * dna
    /\ dna' = 0
    /\ primers' = primers
    /\ hybrids' = hybrids
    /\ phase' = "cooling"

(* Cooling action: lowers temperature to allow annealing *)
Cool ==
    /\ phase = "cooling"
    /\ temp' = "warm"
    /\ primers' = primers
    /\ dna' = dna
    /\ templates' = templates
    /\ hybrids' = hybrids
    /\ phase' = "annealing"

(* Annealing action: primers bind to templates nondeterministically
   Consumes some number n of primers and templates to form hybrids *)
Anneal ==
    /\ phase = "annealing"
    /\ temp = "warm"
    /\ \E n \in 0..MaxConsume :
        /\ n <= primers
        /\ n <= templates
        /\ primers' = primers - n
        /\ templates' = templates - n
        /\ hybrids' = hybrids + n
        /\ dna' = dna
        /\ temp' = temp
        /\ phase' = "extension"

(* Extension action: DNA polymerase extends primers to form new DNA strands
   Hybrids are converted back - each hybrid becomes a complete strand that pairs *)
Extend ==
    /\ phase = "extension"
    /\ temp' = "warm"
    /\ dna' = dna + hybrids
    /\ templates' = templates + hybrids
    /\ hybrids' = 0
    /\ primers' = primers
    /\ phase' = "heating"

(* Next state relation *)
Next ==
    \/ Heat
    \/ Cool
    \/ Anneal
    \/ Extend

(* Fairness: weak fairness on all actions to ensure progress *)
Fairness ==
    /\ WF_vars(Heat)
    /\ WF_vars(Cool)
    /\ WF_vars(Anneal)
    /\ WF_vars(Extend)

(* Complete specification with fairness *)
Spec == Init /\ [][Next]_vars /\ Fairness

=============================================================================