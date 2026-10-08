```tla
MODULE RandomFunctionSample
EXTENDS Integers, TLC, FiniteSets

CONSTANTS Domain, Codomain

VARIABLES functions, sample

Init ==
  /\ functions = [x \in Domain |-> y \in Codomain]
  /\ sample = RandomSubset(functions, 1000)

Next ==
  UNCHANGED <<functions, sample>>

Spec ==
  Init /\ [][Next]_<<functions, sample>>

THEOREM Spec => [](sample \subseteq functions)
```