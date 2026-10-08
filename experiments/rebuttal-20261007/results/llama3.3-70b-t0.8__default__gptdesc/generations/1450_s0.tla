```
MODULE SamplingSystem
EXTENDS Integers, FiniteSets
CONSTANTS S, T, RandomSubset
VARIABLES x

Init == x \in RandomSubset(1000, [S -> T])

Next == UNCHANGED x

Spec == Init /\ [][Next]_x

Inv == TRUE

THEOREM Spec => []Inv
```
Note: This TLA+ module uses the `UNCHANGED` operator to express stuttering steps where the value of `x` does not change. The `RandomSubset` constant is assumed to be defined elsewhere, possibly in a separate module or using a PlusCal algorithm that generates a random subset of the function set `[S -> T]`.