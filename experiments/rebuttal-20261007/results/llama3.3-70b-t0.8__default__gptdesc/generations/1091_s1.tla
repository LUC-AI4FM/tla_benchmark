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
    /\ primers' \in [primers - x |-> x \in 0..Min(primers, templates)]
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
  /\ Init
  /\ [][Next]_<<primers, templates, hybrids, dna, temperature, phase>>
  /\ WF_(phase = "annealing")(phase' = "extension")
  /\ []<>(primers = 0)

TypeInvariant ==
  /\ primers \in Nat
  /\ templates \in Nat
  /\ hybrids \in Nat
  /\ dna \in Nat

CountPreservationInvariant ==
  /\ (primers + templates + hybrids + dna)' = (primers + templates + hybrids + dna)
```
Note: The above TLA+ module assumes that the MaxPrimers, MaxTemplates, MaxHybrids, and MaxDNA constants are defined elsewhere in the system. The `Min` function is used to calculate the minimum of two values.