```
MODULE FastMutex
EXTENDS Integers, FiniteSets

CONSTANTS M, N

VARIABLES x, y, b, pc

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = FALSE
  /\ pc \in ([1..N] -> {"try", "crit", "exit"})

Next ==
  \/ \E i \in 1..M : Next_i
  \/ \E j \in (M+1)..N : Next_j

Next_i ==
  /\ pc[i] = "try"
  /\ x' = i
  /\ y' = IF y = 0 THEN i ELSE y
  /\ b' = FALSE
  /\ pc' = [pc EXCEPT ![i] = "crit"]
  /\ UNCHANGED <<x, y, b, pc>>

Next_j ==
  /\ pc[j] = "try"
  /\ x' = j
  /\ y' = IF y = 0 THEN j ELSE y
  /\ b' = FALSE
  /\ pc' = [pc EXCEPT ![j] = "crit"]
  /\ UNCHANGED <<x, y, b, pc>>

Spec ==
  /\ Init
  /\ [][Next]_<<x, y, b, pc>>
  /\ WF_vars(<<1..M>>, Next_i)
  /\ WF_vars((M+1)..N, Next_j)

MutualExclusion ==
  \A i, j \in 1..N : 
    \/ i = j
    \/ pc[i] # "crit"
    \/ pc[j] # "crit"

Liveness == <> <>(\E i \in 1..N : pc[i] = "crit")

THEOREM Spec => []MutualExclusion /\ Liveness
```