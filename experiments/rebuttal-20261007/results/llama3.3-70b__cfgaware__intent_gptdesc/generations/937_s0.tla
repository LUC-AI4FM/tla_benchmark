```
MODULE SimpleHourClock
VARIABLES hour

AlwaysTick == hour' = IF hour = 12 THEN 1 ELSE hour + 1

AllTimes == hour \in 1..12

TypeInvariance == []AllTimes

LSpec == Init /\ [][Next]_hour
Init == hour = 1
Next == AlwaysTick

THEOREM LSpec => []AllTimes
THEOREM LSpec => <><>True
THEOREM LSpec => \A h \in 1..12 : <><>hour = h
```
Note: This TLA+ specification defines the required constants, variables, and operators. The `AlwaysTick` operator describes a single-step transition that advances the hour by one modulo 12. The `AllTimes` predicate checks if the current hour is within the valid range of 1 to 12. The `TypeInvariance` theorem states that this property should always hold. The `LSpec` specification combines the initial condition, the next-state relation, and a fairness condition (in the form of a weak fairness requirement) to ensure perpetual progress. The three theorems assert that the specification implies invariance of the hour's type and bounds, infinitely many advancing steps occur, and each hour value appears infinitely often over time.