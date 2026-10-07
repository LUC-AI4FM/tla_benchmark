```tla
MODULE LamportFastMutualExclusion
EXTENDS Integers, FiniteSets

CONSTANTS N

VARIABLES x, y, b, j, failed, inCS

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in 1..N |-> FALSE]
  /\ j = [i \in 1..N |-> 0]
  /\ failed = [i \in 1..N |-> FALSE]
  /\ inCS = [i \in 1..N |-> FALSE]

Next ==
  \/ \E i \in 1..N :
      /\ ~failed[i]
      /\ b[i] = FALSE
      /\ j[i] = 0
      /\ x' = i
      /\ b' = [b EXCEPT ![i] = TRUE]
      /\ y' = y
      /\ j' = [j EXCEPT ![i] = 1]
      /\ failed' = failed
      /\ inCS' = inCS
  \/ \E i \in 1..N :
      /\ ~failed[i]
      /\ b[i] = TRUE
      /\ j[i] = 1
      /\ y # 0
      /\ x' = x
      /\ b' = b
      /\ y' = y
      /\ j' = [j EXCEPT ![i] = 2]
      /\ failed' = failed
      /\ inCS' = inCS
  \/ \E i \in 1..N :
      /\ ~failed[i]
      /\ b[i] = TRUE
      /\ j[i] = 1
      /\ y = 0
      /\ x' = x
      /\ b' = b
      /\ y' = i
      /\ j' = [j EXCEPT ![i] = 3]
      /\ failed' = failed
      /\ inCS' = inCS
  \/ \E i \in 1..N :
      /\ ~failed[i]
      /\ b[i] = TRUE
      /\ j[i] = 3
      /\ x # i
      /\ x' = x
      /\ b' = [b EXCEPT ![i] = FALSE]
      /\ y' = y
      /\ j' = [j EXCEPT ![i] = 4]
      /\ failed' = failed
      /\ inCS' = inCS
  \/ \E i \in 1..N :
      /\ ~failed[i]
      /\ b[i] = FALSE
      /\ j[i] = 4
      /\ \A k \in 1..N : b[k] = FALSE
      /\ x' = x
      /\ b' = b
      /\ y' = y
      /\ j' = [j EXCEPT ![i] = 5]
      /\ failed' = failed
      /\ inCS' = inCS
  \/ \E i \in 1..N :
      /\ ~failed[i]
      /\ b[i] = FALSE
      /\ j[i] = 5
      /\ y # i
      /\ x' = x
      /\ b' = b
      /\ y' = y
      /\ j' = [j EXCEPT ![i] = 6]
      /\ failed' = failed
      /\ inCS' = inCS
  \/ \E i \in 1..N :
      /\ ~failed[i]
      /\ b[i] = FALSE
      /\ j[i] = 5
      /\ y = i
      /\ x' = x
      /\ b' = b
      /\ y' = y
      /\ j' = [j EXCEPT ![i] = 7]
      /\ failed' = failed
      /\ inCS' = inCS
  \/ \E i \in 1..N :
      /\ ~failed[i]
      /\ b[i] = FALSE
      /\ j[i] = 6
      /\ y = 0
      /\ x' = x
      /\ b' = b
      /\ y' = y
      /\ j' = [j EXCEPT ![i] = 7]
      /\ failed' = [failed EXCEPT ![i] = TRUE]
      /\ inCS' = inCS
  \/ \E i \in 1..N :
      /\ ~failed[i]
      /\ b[i] = FALSE
      /\ j[i] = 7
      /\ x' = x
      /\ b' = [b EXCEPT ![i] = TRUE]
      /\ y' = y
      /\ j' = [j EXCEPT ![i] = 0]
      /\ failed' = failed
      /\ inCS' = [inCS EXCEPT ![i] = TRUE]

Invariant ==
  \A i, k \in 1..N : i # k => ~(inCS[i] /\ inCS[k] /\ ~failed[i] /\ ~failed[k])

Liveness ==
  <>[]<>(\E i \in 1..N : inCS[i] /\ ~failed[i])

Spec ==
  /\ Init
  /\ [][Next]_x, y, b, j, failed, inCS
  /\ WF(Next, x, y, b, j, failed, inCS)

THEOREM Spec => []Invariant
THEOREM Spec => Liveness
```