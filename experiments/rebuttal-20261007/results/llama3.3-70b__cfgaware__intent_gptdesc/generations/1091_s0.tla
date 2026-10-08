```
MODULE PCR
VARIABLES doubleStranded, singleStranded, primers, hybrids, temperature
CONSTANTS initialDoubleStranded, initialSingleStranded, initialPrimers, highTemperature, annealingTemperature, extensionTemperature

TypeOK == 
  /\ doubleStranded \in Nat
  /\ singleStranded \in Nat
  /\ primers \in Nat
  /\ hybrids \in Nat
  /\ temperature \in {highTemperature, annealingTemperature, extensionTemperature}

primerPositive == primers > 0

preservationInvariant == 
  (doubleStranded + singleStranded + hybrids) = initialDoubleStranded + initialSingleStranded

preservationProperty == 
  []<> (TypeOK /\ preservationInvariant)

Spec == 
  /\ TypeOK
  /\ [][
      \/ (temperature = highTemperature /\ doubleStranded' = 0 /\ singleStranded' = initialDoubleStranded + initialSingleStranded /\ primers' = primers /\ hybrids' = 0)
      \/ (temperature = annealingTemperature /\ doubleStranded' = doubleStranded /\ singleStranded' = singleStranded - 1 /\ primers' = primers - 1 /\ hybrids' = hybrids + 1)
      \/ (temperature = extensionTemperature /\ doubleStranded' = doubleStranded + hybrids /\ singleStranded' = singleStranded /\ primers' = primers /\ hybrids' = 0)
      \/ (temperature' = highTemperature /\ temperature = annealingTemperature)
      \/ (temperature' = annealingTemperature /\ temperature = highTemperature)
      \/ (temperature' = extensionTemperature /\ temperature = annealingTemperature)
  ]_

THEOREM preservationProperty => []<>(doubleStranded > initialDoubleStranded)

THEOREM primerPositive => <>[](primers = 0)
```
Note: The `Spec` definition uses the `_` operator to indicate that the next state is chosen nondeterministically from the set of possible next states. This allows for the model to exhibit different behaviors while still respecting the constraints and invariants defined by the specification.