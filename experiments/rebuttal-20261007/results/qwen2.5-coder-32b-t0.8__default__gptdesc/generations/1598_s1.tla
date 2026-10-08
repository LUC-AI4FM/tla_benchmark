```tla
MODULE FastMutualExclusion

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N

VARIABLES x, y, b, S

Init == /\ x = 1
        /\ y = 1
        /\ \A i \in 1..N : b[i] = FALSE
        /\ \A i \in 1..N : S[i] = {}

Next == \/ /\ x > 0
          /\ \/ \E i \in 1..N : ~b[i]
             /\ \/ y = 1
                /\ x' = (CHOOSE j \in 1..N : ~b[j])
                /\ b[x']'
                /\ S[x']' = {x'}
                   []
                /\ y' = x
                /\ b[y] = TRUE
                /\ \A j \in S[y] : b[j]'
                /\ S[y]' = {}
             []
          /\ \/ \E i \in 1..N : ~b[i]
             /\ y > 0
             /\ y' = (CHOOSE j \in 1..N : ~b[j])
             /\ b[y']'
             /\ S[y']' = {y'}
        []
        \/ /\ x > 0
           /\ y > 0
           /\ (\E i \in 1..N : ~b[i] => (x' = (CHOOSE j \in 1..N : ~b[j]) /\ b[x']'))
           /\ (\A i \in S[y] : b[i]' \/ S[y]' = {})

MutualExclusion == \A i, j \in 1..N : i # j => ~(x = i) \/ ~(y = j)

Spec ==
    /\ Init
    /\ [][Next]_<<x, y, <<b>>, <<S>>>
    /\ WF_next(Next)
    /\ []<>(\E i \in 1..N : x = i \/ y = i)

END FastMutualExclusion
```