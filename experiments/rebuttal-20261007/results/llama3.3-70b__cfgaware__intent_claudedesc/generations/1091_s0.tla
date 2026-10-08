---------------------------- MODULE PCR --------------------------------
EXTENDS Integers, Naturals

CONSTANT InitialPrimers, InitialDNA

VARIABLE doubleStrandedDNA, singleStrandedTemplates, primers, templatePrimerHybrids, temperature

TypeOK == doubleStrandedDNA \in Nat & singleStrandedTemplates \in Nat & 
          primers \in Nat & templatePrimerHybrids \in Nat & 
          temperature \in {"high", "medium", "warm", "moderate"}

primerPositive == primers > 0

preservationInvariant == 
  primers + singleStrandedTemplates + 2 * doubleStrandedDNA + 2 * templatePrimerHybrids = 
  InitialPrimers + 2 * InitialDNA

preservationProperty == [] preservationInvariant

Spec ==
  /\ TypeOK
  /\ doubleStrandedDNA = InitialDNA
  /\ singleStrandedTemplates = 0
  /\ primers = InitialPrimers
  /\ templatePrimerHybrids = 0
  /\ temperature = "moderate"
  /\ [][
      /\ (temperature = "high" 
          /\ doubleStrandedDNA' = 0 
          /\ singleStrandedTemplates' = singleStrandedTemplates + doubleStrandedDNA 
          /\ primers' = primers + templatePrimerHybrids 
          /\ templatePrimerHybrids' = 0
          /\ temperature' = "warm")
       \/ (temperature = "high" 
           /\ doubleStrandedDNA' = doubleStrandedDNA 
           /\ singleStrandedTemplates' = singleStrandedTemplates 
           /\ primers' = primers 
           /\ templatePrimerHybrids' = templatePrimerHybrids
           /\ temperature' = "high")
       \/ (temperature = "warm" 
           /\ doubleStrandedDNA' = doubleStrandedDNA 
           /\ singleStrandedTemplates' = singleStrandedTemplates - p 
           /\ primers' = primers - p 
           /\ templatePrimerHybrids' = templatePrimerHybrids + p
           /\ temperature' = "medium"
           /\ p \in 0..Min(primers, singleStrandedTemplates))
       \/ (temperature = "warm" 
           /\ doubleStrandedDNA' = doubleStrandedDNA 
           /\ singleStrandedTemplates' = singleStrandedTemplates 
           /\ primers' = primers 
           /\ templatePrimerHybrids' = templatePrimerHybrids
           /\ temperature' = "warm")
       \/ (temperature = "medium" 
           /\ doubleStrandedDNA' = doubleStrandedDNA + templatePrimerHybrids 
           /\ singleStrandedTemplates' = singleStrandedTemplates 
           /\ primers' = primers 
           /\ templatePrimerHybrids' = 0
           /\ temperature' = "high")
       \/ (temperature = "medium" 
           /\ doubleStrandedDNA' = doubleStrandedDNA 
           /\ singleStrandedTemplates' = singleStrandedTemplates 
           /\ primers' = primers 
           /\ templatePrimerHybrids' = templatePrimerHybrids
           /\ temperature' = "medium")
      /\ preservationInvariant'
  ]

=============================================================================