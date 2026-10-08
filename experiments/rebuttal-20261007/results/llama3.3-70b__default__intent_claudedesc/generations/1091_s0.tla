```
MODULE PCR
EXTENDS Integers

CONSTANTS InitialDNA, InitialPrimers
VARIABLES dsDNA, ssTemplates, primers, hybrids, temperature

Init ==
  /\ dsDNA = InitialDNA
  /\ ssTemplates = 0
  /\ primers = InitialPrimers
  /\ hybrids = 0
  /\ temperature = "moderate"

Next ==
  \/ (temperature = "moderate" /\ dsDNA > 0 /\ 
      /\ dsDNA' = dsDNA - 1
      /\ ssTemplates' = ssTemplates + 2
      /\ primers' = primers + 1
      /\ hybrids' = hybrids
      /\ temperature' = "high")
  \/ (temperature = "moderate" /\ dsDNA = 0 /\ 
      /\ dsDNA' = dsDNA
      /\ ssTemplates' = ssTemplates
      /\ primers' = primers
      /\ hybrids' = hybrids
      /\ temperature' = "high")
  \/ (temperature = "high" /\ 
      /\ dsDNA' = 0
      /\ ssTemplates' = InitialDNA * 2 + ssTemplates
      /\ primers' = InitialPrimers + hybrids
      /\ hybrids' = 0
      /\ temperature' = "cooling")
  \/ (temperature = "cooling" /\ 
      /\ dsDNA' = dsDNA
      /\ ssTemplates' = ssTemplates
      /\ primers' = primers
      /\ hybrids' = hybrids
      /\ temperature' = "warm")
  \/ (temperature = "warm" /\ 
      /\ dsDNA' = dsDNA
      /\ ssTemplates' = ssTemplates - numAnneal
      /\ primers' = primers - numAnneal
      /\ hybrids' = hybrids + numAnneal
      /\ temperature' = "medium"
      /\ numAnneal \in 0..Min(primers, ssTemplates))
  \/ (temperature = "medium" /\ 
      /\ dsDNA' = dsDNA + hybrids
      /\ ssTemplates' = ssTemplates
      /\ primers' = primers
      /\ hybrids' = 0
      /\ temperature' = "moderate")

Spec == Init /\ [][Next]_<<dsDNA, ssTemplates, primers, hybrids, temperature>>
Inv == (primers + ssTemplates + 2 * dsDNA + 2 * hybrids) = InitialPrimers + 2 * InitialDNA

THEOREM Spec => []Inv
THEOREM Spec => <<Inv>>_
```
Note: `numAnneal` is a nondeterministic variable representing the number of primers that anneal to templates in each step, and `Min(primers, ssTemplates)` represents the minimum between the current counts of primers and single-stranded templates.