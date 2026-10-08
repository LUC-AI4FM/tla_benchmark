```tla
MODULE FastMutualExclusion

EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES x, y, b, pc

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in 1..N |-> FALSE]
  /\ pc = [i \in 1..N |-> "Noncritical"]

Next ==
  \/ \E i \in 1..N :
      pc[i] = "Noncritical"
      /\ pc' = [pc EXCEPT ![i] = "Try"]
      /\ x' = x
      /\ y' = y
      /\ b' = b
  \/ \E i \in 1..N :
      pc[i] = "Try"
      /\ b'[i] = TRUE
      /\ IF x = 0
         THEN x' = i
         ELSE x' = x
      /\ y' = y
      /\ pc' = [pc EXCEPT ![i] = "Waiting"]
      /\ b = [b EXCEPT ![i] = FALSE]
  \/ \E i \in 1..N :
      pc[i] = "Waiting"
      /\ x = i
      /\ IF y = 0
         THEN y' = i
         ELSE y' = y
      /\ pc' = [pc EXCEPT ![i] = "Critical"]
      /\ b' = b
      /\ x' = x
  \/ \E i \in 1..N :
      pc[i] = "Critical"
      /\ pc' = [pc EXCEPT ![i] = "Exit"]
      /\ y' = 0
      /\ x' = 0
      /\ b' = [b EXCEPT ![i] = FALSE]
  \/ \E i \in 1..N :
      pc[i] = "Exit"
      /\ pc' = [pc EXCEPT ![i] = "Noncritical"]
      /\ b' = b
      /\ x' = x
      /\ y' = y

Spec ==
  Init /\ [][Next]_<<x, y, b, pc>>

MutualExclusion ==
  \A i, j \in 1..N :
    ~ (pc[i] = "Critical" /\ pc[j] = "Critical" /\ i # j)

THEOREM Spec => []MutualExclusion

Fairness == 
  \A i \in 1..N :
    WF Вар(pc, "Try")_<<x, y, b, pc>>
  /\ WF Вар(pc, "Waiting")_<<x, y, b, pc>>
  /\ WF Вар(pc, "Critical")_<<x, y, b, pc>>
  /\ WF Вар(pc, "Exit")_<<x, y, b, pc>>

Liveness == Spec /\ Fairness

ConditionalLiveness == 
  \A i \in 1..N :
    <>(pc[i] = "Try")
```