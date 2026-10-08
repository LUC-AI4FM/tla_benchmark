```
MODULE FastMutualExclusion
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES x, y, b, j, failed

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in 1..N |-> FALSE]
  /\ j = [i \in 1..N |-> 0]
  /\ failed = [i \in 1..N |-> FALSE]

Try ==
  /\ \E i \in 1..N :
      /\ x = 0
      /\ b[i] = TRUE
      /\ j[i] = 1
      /\ x' = i
      /\ y' = 0
      /\ b' = [b EXCEPT ![i] = FALSE]
      /\ j' = [j EXCEPT ![i] = 2]
      /\ failed' = failed
  /\ \A k \in 1..N \ {i} :
      /\ x' = x
      /\ y' = y
      /\ b' = b
      /\ j' = j
      /\ failed' = failed

Critical ==
  /\ \E i \in 1..N :
      /\ y = 0
      /\ j[i] = 2
      /\ x' = x
      /\ y' = i
      /\ b' = b
      /\ j' = [j EXCEPT ![i] = 3]
      /\ failed' = failed
  /\ \A k \in 1..N \ {i} :
      /\ x' = x
      /\ y' = y
      /\ b' = b
      /\ j' = j
      /\ failed' = failed

Exit ==
  /\ \E i \in 1..N :
      /\ y = i
      /\ j[i] = 3
      /\ x' = 0
      /\ y' = 0
      /\ b' = [b EXCEPT ![i] = FALSE]
      /\ j' = [j EXCEPT ![i] = 0]
      /\ failed' = failed
  /\ \A k \in 1..N \ {i} :
      /\ x' = x
      /\ y' = y
      /\ b' = b
      /\ j' = j
      /\ failed' = failed

Retry ==
  /\ \E i \in 1..N :
      /\ x # 0
      /\ x # i
      /\ b[i] = TRUE
      /\ j[i] = 2
      /\ x' = x
      /\ y' = y
      /\ b' = [b EXCEPT ![i] = FALSE]
      /\ j' = [j EXCEPT ![i] = 0]
      /\ failed' = [failed EXCEPT ![i] = TRUE]
  /\ \A k \in 1..N \ {i} :
      /\ x' = x
      /\ y' = y
      /\ b' = b
      /\ j' = j
      /\ failed' = failed

Next ==
  Try \/ Critical \/ Exit \/ Retry

MutualExclusion == y \in 1..N \/ y = 0

Spec == Init /\ [][Next]_<<x, y, b, j, failed>>
          /\ WF_<<x, y, b, j, failed>>(Try)
          /\ WF_<<x, y, b, j, failed>>(Critical)
          /\ WF_<<x, y, b, j, failed>>(Exit)
          /\ WF_<<x, y, b, j, failed>>(Retry)

THEOREM Spec => []MutualExclusion
THEOREM Spec => <><y # 0>_
```