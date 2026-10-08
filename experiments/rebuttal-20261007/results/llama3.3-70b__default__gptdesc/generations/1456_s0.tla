```
MODULE TinyStateMachine
EXTENDS Integers, TLC
CONSTANTS 
VARIABLES x, y

Init == (x = {} /\ y = {1, 2, 3})
Next == (y' = y) /\ (x' ⊆ y')
FullSet(x) == (x = {1, 2, 3})
GainThree(x, x') == (3 \in x') /\ (3 \notin x)

Spec == Init ∧ [][Next]_<<x, y>>
THEOREM TLCGet("FullSet") = 5
THEOREM TLCGet("GainThree") = 3

=============================================================================
```
Note: The `TLC` module and its functions like `TLCGet` are not standard TLA+ but rather specific to the TLC model checker. This specification is tailored to work with the TLC model checker for inspecting named-state exploration metadata.