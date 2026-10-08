```
MODULE LamportFastMutex
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES x, y, b, cs

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in 1..N |-> FALSE]
  /\ cs = {}

Next ==
  \/ \E i \in 1..N :
    /\ b[i] = FALSE
    /\ x' = i
    /\ IF y = 0 THEN y' = i ELSE y' = y
    /\ b' = [b EXCEPT ![i] = TRUE]
    /\ cs' = cs
  \/ \E i \in 1..N :
    /\ b[i] = TRUE
    /\ x = i
    /\ y = i
    /\ \A j \in 1..N : j # i => ~b[j]
    /\ cs' = cs \cup {i}
    /\ x' = x
    /\ y' = y
    /\ b' = [b EXCEPT ![i] = FALSE]
  \/ \E i \in 1..N :
    /\ b[i] = TRUE
    /\ x = i
    /\ y # i
    /\ cs' = cs
    /\ x' = x
    /\ y' = y
    /\ b' = [b EXCEPT ![i] = FALSE]
  \/ \E i \in 1..N :
    /\ b[i] = TRUE
    /\ y # 0
    /\ y' = 0
    /\ x' = x
    /\ cs' = cs
    /\ b' = b

Spec ==
  Init /\ [][Next]_<<x, y, b, cs>>
 WF_vars == <<x, y, b, cs>>

THEOREM Spec => []~(EXISTS <<i, j>> \in (1..N)\X(1..N) : i # j /\ {i, j} \subseteq cs)
THEOREM Spec => <><cs # {}>_
```