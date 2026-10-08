```tla
MODULE FastMutualExclusion

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N
ASSUME N \in Nat \ {0}

VARIABLES x, y, b, S

Init == /\ x = 1
        /\ y = 1
        /\ b = [i \in 1..N -> FALSE]
        /\ S = [i \in 1..N -> {}]

Next ==
    \/ /\ \E i \in 1..N : \A j \in 1..N \ {i} : j \notin S[i]
       /\ \/ x = 1
          /\ \/ b[i] = FALSE
             /\ \/ y = i
                /\ y' = 1
                /\ S' = [S EXCEPT ![i] = {}]
                /\ b' = [b EXCEPT ![i] = TRUE]
                /\ x' = i
             /\ \/ b[i] = TRUE
                /\ \/ y = 1
                   /\ y' = i
                   /\ b' = [b EXCEPT ![i] = FALSE]
                /\ \/ y \in 1..N \ {i}
                   /\ S' = [S EXCEPT ![y] = S[y] \cup {i}]
       \/ x \in 1..N \ {i}
          /\ \/ i \notin S[x]
             /\ b[x] = FALSE
                /\ b' = [b EXCEPT ![x] = TRUE]
                /\ y' = i
                /\ S' = [S EXCEPT ![y'] = {}]
             /\ \/ i \in S[x]
                /\ y' = 1
                /\ b' = [b EXCEPT ![x] = FALSE]

MutualExclusion == \A i, j \in 1..N : i # j => ~ (x = i) \/ ~ (y = j)

Spec ==
    /\ Init
    /\ [][Next]_<<x, y, b, S>>
    /\ WF_[Next]_<<x, y, b, S>>

Liveness == <>[](\E i \in 1..N : x = i)
```