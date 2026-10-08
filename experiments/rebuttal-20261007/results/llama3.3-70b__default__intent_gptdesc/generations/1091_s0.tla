```
MODULE PCR
EXTENDS Integers, Naturals

CONSTANTS HighTemp, AnnealingTemp, ExtensionTemp, InitialDoubleStranded, InitialSingleStranded, InitialPrimer1, InitialPrimer2

VARIABLES doubleStranded, singleStranded, primer1, primer2, hybrids, temperature, cycle

Init ==
  /\ doubleStranded = InitialDoubleStranded
  /\ singleStranded = InitialSingleStranded
  /\ primer1 = InitialPrimer1
  /\ primer2 = InitialPrimer2
  /\ hybrids = 0
  /\ temperature = HighTemp
  /\ cycle = 0

Next ==
  \/ \* Denaturation \*
    (temperature = HighTemp
      /\ doubleStranded' = 0
      /\ singleStranded' = singleStranded + InitialDoubleStranded
      /\ primer1' = primer1
      /\ primer2' = primer2
      /\ hybrids' = 0
      /\ temperature' = AnnealingTemp
      /\ cycle' = cycle + 1)
  \/ \* Annealing \*
    (temperature = AnnealingTemp
      /\ doubleStranded' = doubleStranded
      /\ singleStranded' = singleStranded - 1
      /\ primer1' = primer1 - 1
      /\ primer2' = primer2 - 1
      /\ hybrids' = hybrids + 1
      /\ temperature' = AnnealingTemp
      /\ cycle' = cycle)
  \/ \* Extension \*
    (temperature = AnnealingTemp
      /\ doubleStranded' = doubleStranded + 1
      /\ singleStranded' = singleStranded
      /\ primer1' = primer1
      /\ primer2' = primer2
      /\ hybrids' = hybrids - 1
      /\ temperature' = ExtensionTemp
      /\ cycle' = cycle)
  \/ \* Extension completion \*
    (temperature = ExtensionTemp
      /\ doubleStranded' = doubleStranded
      /\ singleStranded' = singleStranded
      /\ primer1' = primer1
      /\ primer2' = primer2
      /\ hybrids' = hybrids
      /\ temperature' = HighTemp
      /\ cycle' = cycle + 1)

Spec == Init /\ [][Next]_<<doubleStranded, singleStranded, primer1, primer2, hybrids, temperature, cycle>>

ConservationInvariant ==
  doubleStranded + singleStranded + hybrids = InitialDoubleStranded + InitialSingleStranded

NonNegativityInvariant ==
  /\ doubleStranded >= 0
  /\ singleStranded >= 0
  /\ primer1 >= 0
  /\ primer2 >= 0
  /\ hybrids >= 0

TemperatureInvariant ==
  temperature \in {HighTemp, AnnealingTemp, ExtensionTemp}

THEOREM Spec => []ConservationInvariant
THEOREM Spec => []NonNegativityInvariant
THEOREM Spec => []TemperatureInvariant

Liveness == <>[]<>(doubleStranded > InitialDoubleStranded)

Fairness == WF_<<doubleStranded, singleStranded, primer1, primer2, hybrids, temperature, cycle>>(Next)
```
Note: This specification uses the `WF` (weak fairness) operator to ensure that the system makes progress and eventually performs infinite cycles. The `Liveness` property states that the system will eventually produce additional double-stranded product if there are sufficient initial primers and templates.