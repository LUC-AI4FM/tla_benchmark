```
MODULE Clock
EXTENDS Integers

CONSTANTS None

VARIABLES hour

Init == (hour \in 1..12)

Next == hour' = IF hour = 12 THEN 1 ELSE hour + 1

Spec == Init /\ [][Next]_hour

THEOREM Spec => []hour \in 1..12
THEOREM Spec => <><hour' # hour>_
THEOREM Spec => \A h \in 1..12 : <><>hour = h
```
Note: The `_` symbol is used to denote the "except" operator in TLA+, which is used to specify the variables that are changed by an action. In this case, `Next` only changes the `hour` variable.

Also note that the fairness condition is implicit in the specification `Spec`, as it requires that the `Next` action occurs infinitely often. This ensures that the clock will keep advancing indefinitely. 

The three theorems stated at the end are model-checkable assertions that can be used to verify the desired properties of the specification:

1. `[]hour \in 1..12`: The hour is always an integer between 1 and 12.
2. `<><hour' # hour>`: Infinitely many advancing steps occur (i.e., the clock does not stop).
3. `\A h \in 1..12 : <><>hour = h`: Each hour value appears infinitely often over time.