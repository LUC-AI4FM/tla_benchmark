```
MODULE TokenRing
EXTENDS Integers

CONSTANTS N, M
VARIABLES counters, tokenPresent

Init ==
  /\ counters \in [1..N -> 0..M-1]
  /\ tokenPresent \in [1..N -> {True, False}]

Next ==
  /\ IF (tokenPresent[1] = True)
    THEN counters' = [counters EXCEPT ![1] = (counters[N] + 1) % M]
    ELSE counters' = counters
  /\ FORALL (i \in 2..N) :
      IF (tokenPresent[i] = False) /\ (counters[i-1] # counters[i])
      THEN counters' = [counters EXCEPT ![i] = counters[i-1]]
      ELSE counters' = counters
  /\ tokenPresent' = [i \in 1..N |-> IF (counters'[i] = counters'[i-1]) THEN True ELSE False]

Spec ==
  Init /\ [][Next]_<<counters, tokenPresent>>

StabilizationProperty ==
  <>[](~(EXISTS <<i, j>> \in (1..N) * (1..N) : i # j /\ counters[i] = counters[j]))

THEOREM Spec => []StabilizationProperty
```