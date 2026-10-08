```
MODULE PCR
EXTENDS Integers

CONSTANTS MaxPrimers, MaxTemplates, MaxHybrids, MaxDNA
VARIABLES primers, templates, hybrids, dna, temperature, phase

Init == (primers = MaxPrimers) ∧ (templates = MaxTemplates) ∧ 
        (hybrids = 0) ∧ (dna = 0) ∧ (temperature = 0) ∧ (phase = "heating")

Next == IF phase = "heating" THEN
            temperature' = temperature + 1 ∧ 
            primers' = primers ∧ templates' = templates ∧ hybrids' = hybrids ∧ dna' = dna ∧ 
            phase' = IF temperature + 1 < 95 THEN "heating" ELSE "cooling"
        ELSE IF phase = "cooling" THEN
            temperature' = temperature - 1 ∧ 
            primers' = primers ∧ templates' = templates ∧ hybrids' = hybrids ∧ dna' = dna ∧ 
            phase' = IF temperature - 1 > 50 THEN "cooling" ELSE "annealing"
        ELSE IF phase = "annealing" THEN
            ∃ consumedPrimers, consumedTemplates ∈ 0..MaxPrimers :
                (consumedPrimers ≤ primers) ∧ (consumedTemplates ≤ templates) ∧ 
                temperature' = temperature ∧ 
                primers' = primers - consumedPrimers ∧ 
                templates' = templates - consumedTemplates ∧ 
                hybrids' = hybrids + consumedPrimers ∧ 
                dna' = dna ∧ 
                phase' = "extension"
        ELSE \* phase = "extension"
            temperature' = temperature ∧ 
            primers' = primers ∧ templates' = templates ∧ 
            hybrids' = 0 ∧ 
            dna' = dna + hybrids ∧ 
            phase' = "heating"

Spec == Init ∧ [][Next]_<<primers, templates, hybrids, dna, temperature, phase>>

TypeInvariant == primers ∈ Int ∧ templates ∈ Int ∧ hybrids ∈ Int ∧ dna ∈ Int ∧ 
                  temperature ∈ Int ∧ phase ∈ {"heating", "cooling", "annealing", "extension"}

NonNegativityInvariant == primers ≥ 0 ∧ templates ≥ 0 ∧ hybrids ≥ 0 ∧ dna ≥ 0

CountPreservationInvariant == (primers + hybrids) = MaxPrimers

Safety == TypeInvariant ∧ NonNegativityInvariant ∧ CountPreservationInvariant

Liveness == <>[]<>(primers = 0)

THEOREM Spec => []Safety
THEOREM Spec => Liveness
```