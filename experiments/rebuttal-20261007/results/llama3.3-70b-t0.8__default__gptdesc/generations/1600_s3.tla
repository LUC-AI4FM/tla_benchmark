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
      /\ b' = [b EXCEPT ![i] = TRUE]
      /\ UNCHANGED <<y, j, failed>>
  \/ \E i \in 1..N :
      /\ x = i
      /\ y = 0
      /\ b' = [b EXCEPT ![i] = FALSE]
      /\ j' = [j EXCEPT ![i] = 1]
      /\ UNCHANGED <<x, failed>>
  \/ \E i \in 1..N :
      /\ x = i
      /\ y = i
      /\ b' = [b EXCEPT ![i] = FALSE]
      /\ j' = [j EXCEPT ![i] = 2]
      /\ UNCHANGED <<x, failed>>
  \/ \E i \in 1..N :
      /\ x = i
      /\ y = i
      /\ b' = b
      /\ j' = [j EXCEPT ![i] = 3]
      /\ failed' = [failed EXCEPT ![i] = TRUE]
      /\ UNCHANGED x

Next ==
  Try
  \/ \E i \in 1..N :
      /\ x = i
      /\ y = i
      /\ j[i] = 3
      /\ b' = [b EXCEPT ![i] = FALSE]
      /\ j' = [j EXCEPT ![i] = 0]
      /\ failed' = [failed EXCEPT ![i] = FALSE]
      /\ x' = 0
      /\ UNCHANGED y

Spec ==
  Init /\ [][Next]_<<x, y, b, j, failed>>
  /\ WF_<<x, y, b, j, failed>>(Try)

MutualExclusion ==
  \A i, j \in 1..N : 
    ~(j[i] = 3 /\ j[j] = 3)

Liveness == <>[](\E i \in 1..N : j[i] = 3)

THEOREM Spec => []MutualExclusion
THEOREM Spec => Liveness
```