---------------------------- MODULE PCR ----------------------------
EXTENDS Naturals

CONSTANTS InitTemp, InitPrimers, InitDNA, InitTemplates, InitHybrids,
          HeatTemp, CoolTemp, AnnealTemp, ExtendTemp

VARIABLES temp, primers, dna, templates, hybrids, phase

vars == <<temp, primers, dna, templates, hybrids, phase>>

Phases == {"heating", "cooling", "annealing", "extension"}

TypeOK == /\ temp \in Nat
          /\ primers \in Nat
          /\ dna \in Nat
          /\ templates \in Nat
          /\ hybrids \in Nat
          /\ phase \in Phases

primerPositive == primers >= 0

\* The total count of primers plus hybrids plus twice the DNA should be preserved
\* This captures that primers are consumed to form hybrids, and hybrids become DNA
\* Actually, we track: primers + hybrids + 2*dna + templates should relate to initial values
\* Simplified: total genetic material is conserved in some form
preservationInvariant == (primers + hybrids + 2 * dna + templates) = 
                         (InitPrimers + InitHybrids + 2 * InitDNA + InitTemplates)

\* Alternative preservation: primers + hybrids stays related to consumption
preservationProperty == primers + hybrids <= InitPrimers + InitHybrids

Init == /\ temp = InitTemp
        /\ primers = InitPrimers
        /\ dna = InitDNA
        /\ templates = InitTemplates
        /\ hybrids = InitHybrids
        /\ phase = "heating"

\* Heating phase: raise temperature to denature DNA into single-stranded templates
Heat == /\ phase = "heating"
        /\ temp' = HeatTemp
        /\ templates' = templates + 2 * dna  \* Each dsDNA becomes 2 ssDNA templates
        /\ dna' = 0
        /\ primers' = primers
        /\ hybrids' = hybrids
        /\ phase' = "cooling"

\* Cooling phase: lower temperature to prepare for annealing
Cool == /\ phase = "cooling"
        /\ temp' = CoolTemp
        /\ primers' = primers
        /\ dna' = dna
        /\ templates' = templates
        /\ hybrids' = hybrids
        /\ phase' = "annealing"

\* Annealing phase: primers bind to templates nondeterministically
\* Some number k of primers and templates form hybrids
Anneal == /\ phase = "annealing"
          /\ temp' = AnnealTemp
          /\ \E k \in 0..primers :
               /\ k <= templates
               /\ primers' = primers - k
               /\ templates' = templates - k
               /\ hybrids' = hybrids + k
               /\ dna' = dna
          /\ phase' = "extension"

\* Extension phase: hybrids are extended by polymerase to form new dsDNA
Extend == /\ phase = "extension"
          /\ temp' = ExtendTemp
          /\ dna' = dna + hybrids  \* Each hybrid becomes a new dsDNA
          /\ hybrids' = 0
          /\ primers' = primers
          /\ templates' = templates
          /\ phase' = "heating"

Next == Heat \/ Cool \/ Anneal \/ Extend

\* Fairness: we require weak fairness on all actions to reason about liveness
Fairness == /\ WF_vars(Heat)
            /\ WF_vars(Cool)
            /\ WF_vars(Anneal)
            /\ WF_vars(Extend)

Spec == Init /\ [][Next]_vars /\ Fairness

\* Liveness property: eventually primers are depleted
\* NOTE: This property does NOT hold in general because annealing can
\* nondeterministically choose k=0, never consuming primers
EventualPrimerDepletion == <>(primers = 0)

=============================================================================