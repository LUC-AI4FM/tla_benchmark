---------------------------- MODULE RandomFunctionSubset ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS n, m, k
VARIABLES functions, subset

Init == (
  /\ functions = [i \in 1..n |-> CHOOSE j \in 1..m]
  /\ subset = ChooseKDistinctFunctions(functions, k)
)

ChooseKDistinctFunctions(set, count) ==
  IF count = 0 THEN {}
  ELSE {f} \cup ChooseKDistinctFunctions(set \ {f}, count - 1)
        WITH f == CHOOSE f \in set

Next == FALSE

Spec == Init /\ [][Next]_subset

THEOREM Spec => []Cardinality(subset) = k
THEOREM Spec => []\A f1, f2 \in subset : f1 # f2
THEOREM Spec => []\A f \in subset : IsValidFunction(f)
THEOREM Spec => <>[]subset' = subset

IsValidFunction(f) == 
  /\ DOMAIN f = 1..n
  /\ RANGE f \subseteq 1..m
  /\ \A x \in DOMAIN f : f[x] \in 1..m

=============================================================================