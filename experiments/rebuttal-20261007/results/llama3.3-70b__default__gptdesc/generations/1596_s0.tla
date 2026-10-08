```
MODULE FastMutex
EXTENDS Integers, FiniteSets

CONSTANTS M, N

VARIABLES x, y, b, pc

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = FALSE
  /\ pc \in [1..N -> {"Noncritical"}]

Next ==
  \/ \E i \in 1..M : Next_i
  \/ \E j \in (M+1)..N : Next_j

Next_i ==
  /\ pc[i] = "Noncritical"
  /\ x' = i
  /\ y' = y
  /\ b' = FALSE
  /\ pc' = [pc EXCEPT ![i] = "Trying"]
  \/ pc[i] = "Trying"
  /\ (y = 0 \/ y = i)
  /\ x' = x
  /\ y' = 0
  /\ b' = TRUE
  /\ pc' = [pc EXCEPT ![i] = "Critical"]
  \/ pc[i] = "Critical"
  /\ x' = x
  /\ y' = y
  /\ b' = FALSE
  /\ pc' = [pc EXCEPT ![i] = "Noncritical"]

Next_j ==
  /\ pc[j] = "Noncritical"
  /\ x' = j
  /\ y' = y
  /\ b' = FALSE
  /\ pc' = [pc EXCEPT ![j] = "Trying"]
  \/ pc[j] = "Trying"
  /\ (y = 0 \/ y = j)
  /\ x' = x
  /\ y' = 0
  /\ b' = TRUE
  /\ pc' = [pc EXCEPT ![j] = "Critical"]
  \/ pc[j] = "Critical"
  /\ x' = x
  /\ y' = y
  /\ b' = FALSE
  /\ pc' = [pc EXCEPT ![j] = "Noncritical"]

MutualExclusion ==
  \A i, j \in 1..N : i # j => ~(pc[i] = "Critical" /\ pc[j] = "Critical")

Spec ==
  Init /\ [][Next]_<<x, y, b, pc>>
  /\ WF_vars(Next_i, <<x, y, b, pc>>) \in 1..M
  /\ WF_vars(Next_j, <<x, y, b, pc>>) \in (M+1)..N

THEOREM Spec => []MutualExclusion
THEOREM Spec => <><pc[i] = "Critical">_i \in 1..N
```