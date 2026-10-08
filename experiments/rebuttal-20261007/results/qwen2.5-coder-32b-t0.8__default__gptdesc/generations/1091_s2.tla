------------------------------ MODULE PCR_Cycle ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS MaxPrimers, MaxTemplates

VARIABLES Temp, Primers, DoubleStrandedDNA, SingleStrandedTemplates, Hybrids

Init == 
  /\ Temp = "Cooling"
  /\ Primers \in 0..MaxPrimers
  /\ DoubleStrandedDNA = 0
  /\ SingleStrandedTemplates \in 0..MaxTemplates
  /\ Hybrids = 0

Next ==
  \/ /\ Temp = "Heating"
     /\ Temp' = "Cooling"
     /\ UNCHANGED <<Primers, DoubleStrandedDNA, SingleStrandedTemplates, Hybrids>>
  \/ /\ Temp = "Cooling"
     /\ Temp' \in {"Annealing", "Extension"}
     /\ UNCHANGED <<Primers, DoubleStrandedDNA, SingleStrandedTemplates, Hybrids>>
  \/ /\ Temp = "Annealing"
     /\ \/ /\ Primers > 0
          /\ SingleStrandedTemplates > 0
          /\ \/ Hybrids' \in 1..Min(Primers, SingleStrandedTemplates)
             /\ Primers' = Primers - Hybrids'
             /\ SingleStrandedTemplates' = SingleStrandedTemplates - Hybrids'
             /\ DoubleStrandedDNA' = DoubleStrandedDNA
        \/ /\ Hybrids' = 0
           /\ Primers' = Primers
           /\ SingleStrandedTemplates' = SingleStrandedTemplates
           /\ DoubleStrandedDNA' = DoubleStrandedDNA
     /\ Temp' = "Cooling"
  \/ /\ Temp = "Extension"
     /\ Hybrids > 0
     /\ Hybrids' = 0
     /\ DoubleStrandedDNA' = DoubleStrandedDNA + Hybrids
     /\ Primers' = Primers
     /\ SingleStrandedTemplates' = SingleStrandedTemplates
     /\ Temp' = "Cooling"

Spec == Init /\ [][Next]_<<Temp, Primers, DoubleStrandedDNA, SingleStrandedTemplates, Hybrids>>

SafetyInvariant ==
  /\ Primers \in 0..MaxPrimers
  /\ DoubleStrandedDNA \in 0..(MaxPrimers * MaxTemplates)
  /\ SingleStrandedTemplates \in 0..MaxTemplates
  /\ Hybrids \in 0..Min(Primers, SingleStrandedTemplates)

LivenessProperty ==
  <>[](Primers = 0)

=============================================================================