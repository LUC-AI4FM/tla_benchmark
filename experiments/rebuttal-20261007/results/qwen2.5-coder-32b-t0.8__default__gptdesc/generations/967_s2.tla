```tla
MODULE StoneCutting

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS W, N

VARIABLES weights

Init == /\ weights \in Seq(Naturals)
        /\ Len(weights) = N
        /\ Sum(weights) = W
        /\ \A i \in 1..N : weights[i] >= 0

Next ==
    CHOOSE n \in (SUBSET {i \in 1..N: weights[i] > 0}) :
        \/ \E j \in n : weights[j]' # weights[j]
        \/ \A j \notin n : weights[j]' = weights[j]

CanMeasure(target) ==
    LET Coefficients == {c \in [1..N -> {-1, 0, 1}]}
    IN  \E c \in Coefficients :
            Sum({j \in 1..N: c[j] * weights[j]}) = target

Safety == /\ Init
          /\ \A target \in 1..W : CanMeasure(target)

Spec ==
    \/ /\ Safety
       /\ [][\E n \in (SUBSET {i \in 1..N: weights[i] > 0}) :
              \/ \E j \in n : weights[j]' # weights[j]
              \/ \A j \notin n : weights[j]' = weights[j]]
    \/ /\ PrintT("No solution exists")
       /\ UNCHANGED weights

WF_Init_Next == WF_vars(Init, Next)

THEOREM Spec => []Safety
```