MODULE PCRSpec
EXTENDS Naturals, TLC

CONSTANTS InitDNA, InitPrimer

VARIABLES dna, template, primer, hybrid, tempState

TempStates == {"High", "Cooling", "Warm", "Medium"}

Min(a,b) == IF a <= b THEN a ELSE b

Init ==
  /\ dna = InitDNA
  /\ template = 0
  /\ primer = InitPrimer
  /\ hybrid = 0
  /\ tempState \in TempStates
  /\ tempState = "High"

Denature ==
  /\ tempState = "High"
  /\ dna' = 0
  /\ hybrid' = 0
  /\ template' = template + 2*dna + hybrid
  /\ primer' = primer + hybrid
  /\ tempState' = "Cooling"

CoolingStep ==
  /\ tempState = "Cooling"
  /\ dna' = dna
  /\ template' = template
  /\ primer' = primer
  /\ hybrid' = hybrid
  /\ tempState' = "Warm"

Anneal ==
  /\ tempState = "Warm"
  /\ \E k \in Nat :
        /\ k <= Min(template, primer)
        /\ template' = template - k
        /\ primer' = primer - k
        /\ hybrid' = hybrid + k
        /\ dna' = dna
        /\ tempState' = "Medium"

Extend ==
  /\ tempState = "Medium"
  /\ dna' = dna + hybrid
  /\ hybrid' = 0
  /\ template' = template
  /\ primer' = primer
  /\ tempState' = "High"

Next == Denature \/ CoolingStep \/ Anneal \/ Extend

vars == <<dna, template, primer, hybrid, tempState>>

ConservationInvariant ==
  (primer + template + 2*dna + 2*hybrid) = (InitPrimer + 2*InitDNA)

Spec == Init /\ [][Next]_vars /\ []ConservationInvariant
=============================================================================