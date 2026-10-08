------------------------------- MODULE PCRCycle -------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS 
    MaxPrimers, MaxTemplates, MaxHybrids, MaxDNA

VARIABLES temp, primers, templates, hybrids, dna

Init == /\ temp \in {HEATING, COOLING, ANNEALING, EXTENSION}
        /\ primers \in 0..MaxPrimers
        /\ templates \in 0..MaxTemplates
        /\ hybrids = 0
        /\ dna = 0

Next ==
    \/ /\ temp = HEATING 
       /\ primers' = primers 
       /\ templates' = templates 
       /\ hybrids' = 0 
       /\ dna' = dna 
       /\ temp' \in {COOLING}
    \/ /\ temp = COOLING 
       /\ primers' = primers 
       /\ templates' = templates 
       /\ hybrids' = hybrids 
       /\ dna' = dna 
       /\ temp' \in {ANNEALING}
    \/ /\ temp = ANNEALING 
       /\ \/ primers' \in 0..primers
          /\ templates' \in 0..templates
          /\ \/ (/\ primers' < primers 
                 /\ templates' < templates)
             \/ (/\ primers' = primers 
                 /\ templates' = templates)
          /\ hybrids' = primers - primers' + templates - templates'
          /\ dna' = dna 
          /\ temp' \in {EXTENSION}
    \/ /\ temp = EXTENSION 
       /\ primers' = primers 
       /\ templates' = templates 
       /\ hybrids' = 0 
       /\ dna' = dna + hybrids
       /\ temp' \in {HEATING}

Spec == Init /\ [][Next]_<<primers, templates, hybrids, dna, temp>>

TypeOK ==
    /\ temp \in {HEATING, COOLING, ANNEALING, EXTENSION}
    /\ primers \in 0..MaxPrimers
    /\ templates \in 0..MaxTemplates
    /\ hybrids \in 0..(primers + templates)
    /\ dna \in 0..MaxDNA

NonNegativity == 
    /\ primers >= 0 
    /\ templates >= 0 
    /\ hybrids >= 0 
    /\ dna >= 0

CountPreservation ==
    \/ temp' = HEATING \/ temp' = COOLING
    \/ /\ temp' = ANNEALING
       /\ (primers + templates) \geq (primers' + templates')
       /\ hybrids = primers - primers' + templates - templates'
    \/ /\ temp' = EXTENSION
       /\ dna = dna' + hybrids

SafetyProperties == 
    TypeOK /\ NonNegativity /\ CountPreservation

Liveness ==
    <>(primers = 0)

SpecWithFairness == Spec /\ WF_next(<<primers, templates, hybrids, dna, temp>>)

THEOREM Spec => []SafetyProperties
THEOREM SpecWithFairness => Liveness

=============================================================================