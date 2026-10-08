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
    /\ j' = [j EXCEPT ![i] = 1]
    /\ y' = 0
    /\ x' = i
    /\ failed' = failed
    /\ UNCHANGED <<y, b, j, failed>>

TestAndSet ==
  /\ \E i \in 1..N :
    /\ x = i
    /\ j[i] = 2
    /\ y' = i
    /\ x' = 0
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ failed' = [failed EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<x, b, j, failed>>

Retry ==
  /\ \E i \in 1..N :
    /\ x = 0
    /\ y = i
    /\ b[i] = TRUE
    /\ j[i] = 2
    /\ failed' = [failed EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<x, y, b, j>>

CriticalSection ==
  /\ \E i \in 1..N :
    /\ x = 0
    /\ y = i
    /\ b[i] = FALSE
    /\ failed' = [failed EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<x, y, b, j>>

Next ==
  \/ Try
  \/ TestAndSet
  \/ Retry
  \/ CriticalSection

MutualExclusion == (x = 0) => (y = 0)

Spec == Init /\ [][Next]_<<x, y, b, j, failed>>
           /\ WF_(Try)(Try)
           /\ WF_(TestAndSet)(TestAndSet)
           /\ WF_(Retry)(Retry)
           /\ WF_(CriticalSection)(CriticalSection)

THEOREM Spec => []MutualExclusion
THEOREM Spec => <>[]<>(y /= 0)
```