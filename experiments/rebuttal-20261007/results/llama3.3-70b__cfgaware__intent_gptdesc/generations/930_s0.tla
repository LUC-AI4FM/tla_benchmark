```
MODULE Clock
VARIABLES hour

HC == hour \in 1..12

HCini == hour = 1

Next == hour' = IF hour = 12 THEN 1 ELSE hour + 1

Spec == HCini /\ [][Next]_hour

THEOREM Spec => []HC
THEOREM Spec => <><>HC
THEOREM Spec => SF_harmless(Next, hour)
```
Note: This TLA+ module defines the required constants and variables. The `HC` constant represents the invariant that the hour is within the range 1..12. The `HCini` constant represents the initial condition where the hour starts at 1. The `Next` operator describes the step relation, which increments the hour by one modulo 12. The `Spec` operator defines the complete specification of the system as an infinite sequence of steps starting from the initial condition.

The provided theorems express the desired properties:

- `Spec => []HC`: The initialization implies that the invariant holds globally (safety).
- `Spec => <><>HC`: This is not directly expressible in TLA+ but we use `THEOREM Spec => SF_harmless(Next, hour)` to ensure liveness.
- `Spec => SF_harmless(Next, hour)`: The step relation implements the modulo-12 increment under fair execution (liveness).

Note that strong fairness is expressed using the `SF_` operator which ensures that if a step is continuously enabled, it will be taken infinitely often. This guarantees that the clock cycles through all 12 values infinitely often.

To model-check these properties with TLC, you would need to create a configuration file specifying the model (Clock), the specification (Spec), and the invariants and properties to check.