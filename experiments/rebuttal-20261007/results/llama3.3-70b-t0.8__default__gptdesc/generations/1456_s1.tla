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

THEOREM TLCGet("FullSet", "NamedPredicates") = 5
THEOREM TLCGet("GainThree", "NamedPredicates") = 2

=============================================================================
```
Note: The above TLA+ module assumes the TLC module is available, which provides the `TLCGet` operator for inspecting named-state exploration metadata. Also note that this specification uses the `_` suffix to denote stuttering steps (where no state change occurs) in the temporal formula `Spec`.