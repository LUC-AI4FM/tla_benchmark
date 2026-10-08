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
    /\ phase' = IF temperature + 1 >= 95 THEN "cooling" ELSE "heating"
  ELSE IF phase = "cooling"
  THEN
    /\ temperature' = temperature - 1
    /\ primers' = primers
    /\ templates' = templates
    /\ hybrids' = hybrids
    /\ dna' = dna
    /\ phase' = IF temperature - 1 <= 55 THEN "annealing" ELSE "cooling"
  ELSE IF phase = "annealing"
  THEN
    /\ temperature' = temperature
    /\ primers' \in [primers - templates, primers]
    /\ templates' \in [templates - (primers - primers'), templates]
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

Spec == Init /\ [][Next]_<<primers, templates, hybrids, dna, temperature, phase>>

TypeInvariant ==
  /\ primers \in Nat
  /\ templates \in Nat
  /\ hybrids \in Nat
  /\ dna \in Nat
  /\ temperature \in Int

CountPreservationInvariant ==
  /\ (primers + hybrids + dna) = MaxPrimers
  /\ (templates + hybrids + dna) = MaxTemplates

Liveness == <> (primers = 0)

THEOREM Spec => []TypeInvariant
THEOREM Spec => []CountPreservationInvariant
THEOREM Spec => Liveness
```