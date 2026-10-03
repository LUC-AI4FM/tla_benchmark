---------------------------- MODULE PCR --------------------------------
EXTENDS Integers

CONSTANT MaxPrimers, MaxTemplates, MaxHybrids, MaxDNA

VARIABLE primers, templates, hybrids, dna, temperature

TypeOK == (primers \in 0..MaxPrimers) /\ 
          (templates \in 0..MaxTemplates) /\ 
          (hybrids \in 0..MaxHybrids) /\ 
          (dna \in 0..MaxDNA) /\ 
          (temperature \in {"heating", "cooling", "annealing", "extension"})

primerPositive == primers > 0

preservationInvariant == (primers + hybrids + dna = MaxPrimers) /\ 
                        (templates + hybrids = MaxTemplates)

Next == ((temperature = "heating") /\ (primers' = primers) /\ 
         (templates' = templates) /\ (hybrids' = hybrids) /\ 
         (dna' = dna) /\ (temperature' = "cooling")) \/
        ((temperature = "cooling") /\ (primers' = primers) /\ 
         (templates' = templates) /\ (hybrids' = hybrids) /\ 
         (dna' = dna) /\ (temperature' = "annealing")) \/
        ((temperature = "annealing") /\ 
         (\E p \in 0..primers : 
           (\E t \in 0..templates : 
             (primers' = primers - p) /\ 
             (templates' = templates - t) /\ 
             (hybrids' = hybrids + p) /\ 
             (dna' = dna) /\ 
             (temperature' = "extension")))) \/
        ((temperature = "extension") /\ 
         (\E h \in 0..hybrids : 
           (primers' = primers) /\ 
           (templates' = templates) /\ 
           (hybrids' = hybrids - h) /\ 
           (dna' = dna + h) /\ 
           (temperature' = "heating")))

Spec == (temperature = "heating") /\ 
       (primers = MaxPrimers) /\ 
       (templates = MaxTemplates) /\ 
       (hybrids = 0) /\ 
       (dna = 0) /\ 
       [][Next]_<<primers, templates, hybrids, dna, temperature>>

preservationProperty == []preservationInvariant

THEOREM Spec => []TypeOK
THEOREM Spec => preservationProperty
THEOREM Spec => <>[]~primerPositive
=============================================================================