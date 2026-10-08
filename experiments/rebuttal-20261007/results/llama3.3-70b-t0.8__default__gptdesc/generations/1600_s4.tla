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
      /\ y' = i
      /\ b' = [b EXCEPT ![i] = FALSE]
      /\ j' = [j EXCEPT ![i] = 2]
      /\ failed' = failed
  /\ \A k \in 1..N \ {i} :
      /\ x' = x
      /\ y' = y
      /\ b'[k] = b[k]
      /\ j'[k] = j[k]
      /\ failed'[k] = failed[k]

Critical ==
  /\ \E i \in 1..N :
      /\ y = i
      /\ j[i] = 2
      /\ x' = 0
      /\ y' = 0
      /\ b' = [b EXCEPT ![i] = FALSE]
      /\ j' = [j EXCEPT ![i] = 0]
      /\ failed' = failed
  /\ \A k \in 1..N \ {i} :
      /\ x' = x
      /\ y' = y
      /\ b'[k] = b[k]
      /\ j'[k] = j[k]
      /\ failed'[k] = failed[k]

Retry ==
  /\ \E i \in 1..N :
      /\ x = i
      /\ j[i] = 2
      /\ b[i] = FALSE
      /\ y' = 0
      /\ b' = [b EXCEPT ![i] = TRUE]
      /\ j' = [j EXCEPT ![i] = 1]
      /\ failed' = [failed EXCEPT ![i] = TRUE]
  /\ \A k \in 1..N \ {i} :
      /\ x' = x
      /\ y' = y
      /\ b'[k] = b[k]
      /\ j'[k] = j[k]
      /\ failed'[k] = failed[k]

Next ==
  \/ Try
  \/ Critical
  \/ Retry

MutualExclusion == (x = 0) \/ (y \in {1,2,...,N})

Spec == Init /\ [][Next]_<<x,y,b,j,failed>>
Liveness == <>[]<>(\E i \in 1..N : j[i] = 2)

THEOREM Spec => []MutualExclusion
THEOREM Spec => Liveness

Fairness == WF_(Try \cup Critical \cup Retry)_vars
SpecWithFairness == Spec /\ Fairness
```