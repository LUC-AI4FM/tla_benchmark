```
MODULE TinyStateMachine
EXTENDS Integers, TLC
CONSTANTS 
VARIABLES x, y

Init == (x = {} /\ y = {1, 2, 3})
Next == (y' = y) /\ (x' ⊆ y')
FullSet(x) == (x = {1, 2, 3})
GainThree(x, x') == (3 \in x') /\ (3 \notin x)

Spec == Init /\ [][Next]_

THEOREM TLCGet("NamedStateCount", "FullSet") = 5
THEOREM TLCGet("NamedStateCount", "GainThree") = 2
```
Note: In the TLA+ code above, I used `_` to represent the temporal operator `always`. Also note that this module uses the TLC module which is a special module for model checking. The `TLCGet` expressions are specific to TLC and may not work in other tools.