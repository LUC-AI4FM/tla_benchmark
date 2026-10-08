```
MODULE TinyStateMachine
EXTENDS Integers, TLC
CONSTANTS 
VARIABLES x, y

Init == (x = {1} /\ y = {1, 2, 3})

Next == (y' = y) /\ (x' ⊆ y')

FullSet(x) == (x = {1, 2, 3})
GainThree(x, x') == (3 \in x') /\ (3 \notin x)

Spec == Init /\ [][Next]_

THEOREM TLCGet("FullSet", "Count") = 5
THEOREM TLCGet("GainThree", "Count") = 1

=============================================================================
```
Note: The `TLCGet` function is used to inspect the named-state exploration metadata, and the expected counts are asserted using the `THEOREM` statement. The `Spec` defines the behavior of the system as an infinite sequence of `Next` steps starting from the initial state defined by `Init`.