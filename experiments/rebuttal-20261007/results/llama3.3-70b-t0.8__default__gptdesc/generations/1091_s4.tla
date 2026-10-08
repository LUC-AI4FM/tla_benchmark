```
MODULE PCR
EXTENDS Integers

CONSTANTS MaxPrimers, MaxTemplates, MaxHybrids, MaxDNA
VARIABLES primers, templates, hybrids, dna, temperature, phase

Init == (
  /\ primers = MaxPrimers
  /\ templates = MaxTemplates
  /\ hybrids = 0
  /\ dna = 0
  /\ temperature = 0
  /\ phase = "heating"
)

Next == IF phase = "heating" THEN
            /\ temperature' = temperature + 1
            /\ primers' = primers
            /\ templates' = templates
            /\ hybrids' = hybrids
            /\ dna' = dna
            /\ phase' = IF temperature' < 95 THEN "heating" ELSE "cooling"
        ELSE IF phase = "cooling" THEN
            /\ temperature' = temperature - 1
            /\ primers' = primers
            /\ templates' = templates
            /\ hybrids' = hybrids
            /\ dna' = dna
            /\ phase' = IF temperature' > 50 THEN "cooling" ELSE "annealing"
        ELSE IF phase = "annealing" THEN
            /\ temperature' = temperature
            /\ primers' \in {primers - x | x \in 0..primers}
            /\ templates' \in {templates - y | y \in 0..templates}
            /\ hybrids' = hybrids + (primers - primers') + (templates - templates')
            /\ dna' = dna
            /\ phase' = "extension"
        ELSE 
            /\ temperature' = temperature
            /\ primers' = primers
            /\ templates' = templates
            /\ hybrids' = 0
            /\ dna' = dna + hybrids
            /\ phase' = "heating"

Spec == Init /\ [][Next]_<<primers, templates, hybrids, dna, temperature, phase>>

TypeInvariant == 
  /\ primers \in Nat
  /\ templates \in Nat
  /\ hybrids \in Nat
  /\ dna \in Nat
  /\ temperature \in Int

CountPreservationInvariant == 
  /\ (primers + templates + hybrids + dna)' = (primers + templates + hybrids + dna)

PrimersDepletion == <>[]primers = 0

THEOREM Spec => []TypeInvariant
THEOREM Spec => []CountPreservationInvariant
THEOREM Spec => PrimersDepletion
```