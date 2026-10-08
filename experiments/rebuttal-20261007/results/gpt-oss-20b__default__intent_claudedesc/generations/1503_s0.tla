MODULE HigherOrderFilter
EXTENDS Naturals

VARIABLE v

FilterSet(S, P, Q) == {x \in S : P(x) /\ Q(x, TRUE)}

Init == 
  v = FilterSet({1,2,3,4,5},
                \lambda x : x > 1,
                \lambda x,y : y = TRUE /\ (x MOD 2 = 1))

Next == v' = v

Spec == Init /\ [][Next]_v
=============================================================================