```
MODULE FastMutex
EXTENDS Integers, FiniteSets

CONSTANTS M, N

VARIABLES x, y, b, pc

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = FALSE
  /\ pc \in ([1..N] -> {"init"})

Next ==
  \/ \E i \in 1..M : Next_i
  \/ \E j \in (M+1)..N : Next_j

Next_i ==
  /\ pc[i] = "init"
  /\ x' = i
  /\ y' = y
  /\ b' = FALSE
  /\ pc' = [pc EXCEPT ![i] = "try"]
  /\ UNCHANGED <<y, b>>

\/ /\ pc[i] = "try"
  /\ (x = 0 \/ x = i)
  /\ y' = i
  /\ b' = TRUE
  /\ pc' = [pc EXCEPT ![i] = "wait"]
  /\ UNCHANGED x

\/ /\ pc[i] = "wait"
  /\ (y = 0 \/ y = i)
  /\ x' = 0
  /\ y' = 0
  /\ b' = FALSE
  /\ pc' = [pc EXCEPT ![i] = "crit"]
  /\ UNCHANGED <<x, y>>

\/ /\ pc[i] = "crit"
  /\ pc' = [pc EXCEPT ![i] = "exit"]
  /\ UNCHANGED <<x, y, b>>

\/ /\ pc[i] = "exit"
  /\ x' = 0
  /\ y' = 0
  /\ b' = FALSE
  /\ pc' = [pc EXCEPT ![i] = "init"]
  /\ UNCHANGED <<y, b>>

Next_j ==
  /\ pc[j] = "init"
  /\ x' = j
  /\ y' = y
  /\ b' = FALSE
  /\ pc' = [pc EXCEPT ![j] = "try"]
  /\ UNCHANGED <<y, b>>

\/ /\ pc[j] = "try"
  /\ (x = 0 \/ x = j)
  /\ y' = j
  /\ b' = TRUE
  /\ pc' = [pc EXCEPT ![j] = "wait"]
  /\ UNCHANGED x

\/ /\ pc[j] = "wait"
  /\ (y = 0 \/ y = j)
  /\ x' = 0
  /\ y' = 0
  /\ b' = FALSE
  /\ pc' = [pc EXCEPT ![j] = "crit"]
  /\ UNCHANGED <<x, y>>

\/ /\ pc[j] = "crit"
  /\ pc' = [pc EXCEPT ![j] = "exit"]
  /\ UNCHANGED <<x, y, b>>

\/ /\ pc[j] = "exit"
  /\ x' = 0
  /\ y' = 0
  /\ b' = FALSE
  /\ pc' = [pc EXCEPT ![j] = "init"]
  /\ UNCHANGED <<y, b>>

Spec == Init /\ [][Next]_<<x, y, b, pc>>
WF1(i \in 1..M) == [](<>pc[i] = "crit")
WF2(j \in (M+1)..N) == [](<>pc[j] = "crit")

THEOREM Spec => []<>(\E k \in 1..N : pc[k] = "crit")
```