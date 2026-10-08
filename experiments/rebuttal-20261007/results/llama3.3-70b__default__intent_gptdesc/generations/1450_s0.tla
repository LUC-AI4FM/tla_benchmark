```
MODULE FunctionSubsetSelection
EXTENDS Integers, FiniteSets

CONSTANTS n, m, k
VARIABLES functions, subset

Init == (
  /\ functions = [i \in 1..n -> j \in 1..m]
  /\ subset = {}
)

Next == (
  /\ subset' = IF subset = {} THEN 
              LET S == {f \in [1..n -> 1..m] : TRUE} IN
                ChooseUniformly(S, k)
            ELSE subset
  /\ functions' = functions
)

Spec == Init /\ [][Next]_<<functions, subset>>

THEOREM Spec => []Cardinality(subset) = k
THEOREM Spec => []\A f \in subset : f \in [1..n -> 1..m]
THEOREM Spec => []\A f1, f2 \in subset : f1 # f2

ChooseUniformly(S, k) == 
  LET R == {s \in SUBSET S : Cardinality(s) = k} IN
    CHOOSE s \in R : TRUE

Fairness == <>[]<>(subset /= {})

TemporalProperties == Spec /\ Fairness

TypeInvariant == 
  /\ functions \in [1..n -> 1..m]
  /\ subset \subseteq [1..n -> 1..m]

THEOREM TemporalProperties => []TypeInvariant
```