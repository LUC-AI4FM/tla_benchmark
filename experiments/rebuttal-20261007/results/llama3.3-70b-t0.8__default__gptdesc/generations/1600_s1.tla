```
MODULE FastMutex
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
      /\ j' = [j EXCEPT ![i] = 1]
      /\ y' = 0
      /\ failed' = failed
      /\ UNCHANGED x

Test ==
  /\ \E i \in 1..N :
      /\ j[i] = 1
      /\ y = 0
      /\ b' = [b EXCEPT ![i] = FALSE]
      /\ y' = i
      /\ failed' = [failed EXCEPT ![i] = FALSE]
      /\ UNCHANGED x
      /\ UNCHANGED j

CriticalSection ==
  /\ \E i \in 1..N :
      /\ y = i
      /\ y' = 0
      /\ b' = b
      /\ j' = [j EXCEPT ![i] = 0]
      /\ failed' = [failed EXCEPT ![i] = TRUE]
      /\ UNCHANGED x

Retry ==
  /\ \E i \in 1..N :
      /\ y /= i
      /\ failed[i]
      /\ b' = [b EXCEPT ![i] = FALSE]
      /\ j' = [j EXCEPT ![i] = 0]
      /\ failed' = [failed EXCEPT ![i] = FALSE]
      /\ UNCHANGED x
      /\ UNCHANGED y

Next ==
  \/ Try
  \/ Test
  \/ CriticalSection
  \/ Retry

MutualExclusion == (y # 0) => (\A i, k \in 1..N : i /= k => ~(j[i] = 3 /\ j[k] = 3))

Spec == Init /\ [][Next]_<<x, y, b, j, failed>>
          /\ WF_vars(Try, <<x, y, b, j, failed>>)
          /\ WF_vars(Test, <<x, y, b, j, failed>>)
          /\ WF_vars(CriticalSection, <<x, y, b, j, failed>>)
          /\ WF_vars(Retry, <<x, y, b, j, failed>>)

THEOREM Spec => []MutualExclusion
THEOREM Spec => <>[]<>(y # 0)
```