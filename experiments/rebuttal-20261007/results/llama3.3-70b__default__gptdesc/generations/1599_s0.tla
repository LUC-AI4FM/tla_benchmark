```
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
      /\ pc[i] = "Noncritical"
      /\ pc' = [pc EXCEPT ![i] = "Try"]
      /\ x' = x
      /\ y' = y
      /\ b' = [b EXCEPT ![i] = TRUE]
  \/ \E i \in 1..N :
      /\ pc[i] = "Try"
      /\ x # 0
      /\ y = i
      /\ pc' = [pc EXCEPT ![i] = "Try1"]
      /\ x' = x
      /\ y' = y
      /\ b' = b
  \/ \E i \in 1..N :
      /\ pc[i] = "Try"
      /\ x = 0
      /\ pc' = [pc EXCEPT ![i] = "Critical"]
      /\ x' = i
      /\ y' = y
      /\ b' = b
  \/ \E i \in 1..N :
      /\ pc[i] = "Try1"
      /\ y # i
      /\ pc' = [pc EXCEPT ![i] = "Noncritical"]
      /\ x' = x
      /\ y' = y
      /\ b' = [b EXCEPT ![i] = FALSE]
  \/ \E i \in 1..N :
      /\ pc[i] = "Critical"
      /\ pc' = [pc EXCEPT ![i] = "Exit"]
      /\ x' = x
      /\ y' = y
      /\ b' = b
  \/ \E i \in 1..N :
      /\ pc[i] = "Exit"
      /\ pc' = [pc EXCEPT ![i] = "Noncritical"]
      /\ x' = 0
      /\ y' = y
      /\ b' = [b EXCEPT ![i] = FALSE]

MutualExclusion ==
  \A i, j \in 1..N : i # j => ~(pc[i] = "Critical" /\ pc[j] = "Critical")

Spec ==
  /\ Init
  /\ [][Next]_<<x, y, b, pc>>
  /\ WF_(<<Try|~(x # 0 /\ y = i)>>)(pc)
  /\ WF_(<<Try1|~(y # i)>>)(pc)
  /\ WF_(<<Critical|~(TRUE)>>)(pc)
  /\ WF_(<<Exit|~(TRUE)>>)(pc)

THEOREM Spec => []MutualExclusion
```