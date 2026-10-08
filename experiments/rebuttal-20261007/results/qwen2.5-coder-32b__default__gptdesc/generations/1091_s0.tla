------------------------------- MODULE PcrCycle -------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS MaxPrimers, MaxTemplates

VARIABLES Temp, Primers, Dna, Templates, Hybrids

Init == /\ Temp \in {HEATING, COOLING, ANNEALING, EXTENSION}
        /\ Primers \in 0..MaxPrimers
        /\ Dna = 0
        /\ Templates \in 0..MaxTemplates
        /\ Hybrids = 0

Next ==
    \/ /\ Temp = HEATING
       /\ Primers' = Primers
       /\ Dna' = Dna
       /\ Templates' = Templates
       /\ Hybrids' = 0
       /\ Temp' = COOLING
    \/ /\ Temp = COOLING
       /\ Primers' = Primers
       /\ Dna' = Dna
       /\ Templates' = Templates
       /\ Hybrids' = 0
       /\ Temp' = ANNEALING
    \/ /\ Temp = ANNEALING
       /\ \E consumedPrimers \in 0..Primers, consumedTemplates \in 0..Templates :
            Primers' = Primers - consumedPrimers
            /\ Templates' = Templates - consumedTemplates
            /\ Hybrids' = consumedPrimers + consumedTemplates
            /\ Dna' = Dna
            /\ Temp' = EXTENSION
    \/ /\ Temp = EXTENSION
       /\ Primers' = Primers
       /\ Templates' = Templates
       /\ Hybrids' = 0
       /\ Dna' = Dna + Hybrids
       /\ Temp' = HEATING

Spec == Init /\ [][Next]_<<Primers, Dna, Templates, Hybrids, Temp>>

\* Safety invariants
TypeOK == Temp \in {HEATING, COOLING, ANNEALING, EXTENSION}
NonNegativity == /\ Primers >= 0
                 /\ Dna >= 0
                 /\ Templates >= 0
                 /\ Hybrids >= 0
CountPreservation == Primers + Dna = [][Primers]_<<Primers>> + [][Dna]_<<Dna>>

\* Liveness property (does not hold)
PrimerDepletion == <>(Primers = 0)

=============================================================================