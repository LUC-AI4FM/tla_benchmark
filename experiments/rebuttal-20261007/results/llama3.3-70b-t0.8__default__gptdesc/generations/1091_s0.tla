```
MODULE PCR
EXTENDS Integers

CONSTANTS MaxPrimers, MaxTemplates, MaxHybrids, MaxDNA
VARIABLES primers, templates, hybrids, dna, temperature, phase

Init ==
  /\ primers = MaxPrimers
  /\ templates = MaxTemplates
  /\ hybrids = 0
  /\ dna = 0
  /\ temperature = 0
  /\ phase = "heating"

Next ==
  IF phase = "heating"
  THEN
    /\ temperature' = temperature + 1
    /\ primers' = primers
    /\ templates' = templates
    /\ hybrids' = hybrids
    /\ dna' = dna
    /\ phase' = IF temperature < 95 THEN "heating" ELSE "cooling"
  ELSE IF phase = "cooling"
  THEN
    /\ temperature' = temperature - 1
    /\ primers' = primers
    /\ templates' = templates
    /\ hybrids' = hybrids
    /\ dna' = dna
    /\ phase' = IF temperature > 50 THEN "cooling" ELSE "annealing"
  ELSE IF phase = "annealing"
  THEN
    /\ temperature' = temperature
    /\ primers' \in [primers - templates, primers]
    /\ templates' = templates - (primers - primers')
    /\ hybrids' = hybrids + (primers - primers')
    /\ dna' = dna
    /\ phase' = "extension"
  ELSE
    /\ temperature' = temperature
    /\ primers' = primers
    /\ templates' = templates
    /\ hybrids' = 0
    /\ dna' = dna + hybrids
    /\ phase' = "heating"

Spec ==
  Init /\ [][Next]_<<primers, templates, hybrids, dna, temperature, phase>>

TypeOK ==
  /\ primers \in Nat
  /\ templates \in Nat
  /\ hybrids \in Nat
  /\ dna \in Nat
  /\ temperature \in Int

CountPreservation ==
  (primers + templates + hybrids + dna)' = (primers + templates + hybrids + dna)

PrimersDeplete ==
  <> (primers = 0)

THEOREM Spec => []TypeOK
THEOREM Spec => []CountPreservation
THEOREM Spec => PrimersDeplete
```