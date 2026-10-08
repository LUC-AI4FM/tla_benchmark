```
MODULE Consensus
EXTENDS TLC

CONSTANTS Values

VARIABLE chosen

vars == <<chosen>>

Init == chosen = {}

Next == ∃ v ∈ Values : (chosen = {} /\ chosen' = {v})

Inv == (chosen = {} \/ ∃ v ∈ Values : chosen = {v}) /\ chosen ⊆ Values

Spec == Init /\ [][Next]_vars
WF_Next == WF(Next)
FullSpec == Spec /\ WF_Next

THEOREM SafetyInvariant == Spec => Inv

THEOREM EventuallyChosen == FullSpec => <> (chosen ≠ {})
```