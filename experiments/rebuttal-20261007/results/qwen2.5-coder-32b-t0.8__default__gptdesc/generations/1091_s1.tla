------------------------------- MODULE PcrCycle -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS MaxPrimerCount, MaxTemplateCount

VARIABLES temperature, primerCount, dsDnaCount, ssTemplateCount, hybridCount

Init == 
  /\ temperature = "heating"
  /\ primerCount \in 0..MaxPrimerCount
  /\ dsDnaCount = 0
  /\ ssTemplateCount \in 0..MaxTemplateCount
  /\ hybridCount = 0

Next ==
  \/ /\ temperature = "heating"
     /\ primerCount' = primerCount
     /\ dsDnaCount' = dsDnaCount
     /\ ssTemplateCount' = ssTemplateCount
     /\ hybridCount' = hybridCount
     /\ temperature' \in {"cooling", "annealing", "extension"}
  \/ /\ temperature = "cooling"
     /\ primerCount' = primerCount
     /\ dsDnaCount' = dsDnaCount
     /\ ssTemplateCount' = ssTemplateCount
     /\ hybridCount' = hybridCount
     /\ temperature' \in {"heating", "annealing", "extension"}
  \/ /\ temperature = "annealing"
     /\ \E consumedPrimers \in 0..primerCount, consumedTemplates \in 0..ssTemplateCount :
          primerCount' = primerCount - consumedPrimers
          /\ dsDnaCount' = dsDnaCount
          /\ ssTemplateCount' = ssTemplateCount - consumedTemplates
          /\ hybridCount' = hybridCount + (consumedPrimers \* consumedTemplates)
          /\ temperature' \in {"heating", "cooling", "extension"}
  \/ /\ temperature = "extension"
     /\ primerCount' = primerCount
     /\ dsDnaCount' = dsDnaCount + hybridCount
     /\ ssTemplateCount' = ssTemplateCount
     /\ hybridCount' = 0
     /\ temperature' \in {"heating", "cooling", "annealing"}

Spec == Init /\ [][Next]_<<temperature, primerCount, dsDnaCount, ssTemplateCount, hybridCount>>

\* Safety invariants
TypeOK ==
  /\ temperature \in {"heating", "cooling", "annealing", "extension"}
  /\ primerCount \in 0..MaxPrimerCount
  /\ dsDnaCount \in 0..(2 * MaxTemplateCount)
  /\ ssTemplateCount \in 0..MaxTemplateCount
  /\ hybridCount \in 0..(MaxPrimerCount * MaxTemplateCount)

Nonnegativity ==
  /\ primerCount >= 0
  /\ dsDnaCount >= 0
  /\ ssTemplateCount >= 0
  /\ hybridCount >= 0

CountPreservation ==
  primerCount + dsDnaCount + ssTemplateCount = 
    primerCount' + dsDnaCount' + ssTemplateCount' - hybridCount' + hybridCount

SafetyProperties == TypeOK /\ Nonnegativity /\ CountPreservation

\* Liveness property
PrimerDepletion ==
  <>(primerCount' = 0)

LivenessProperties == PrimerDepletion

TemporalProperties == \A s \in State: SafetyProperties[s] /\ LivenessProperties

THEOREM Spec => []TemporalProperties

=============================================================================