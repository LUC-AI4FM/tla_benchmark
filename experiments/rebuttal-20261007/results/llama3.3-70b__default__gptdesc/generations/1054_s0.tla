```
MODULE TokenRing
EXTENDS Integers

CONSTANTS N, M
VARIABLES counters

Init ==
  /\ counters \in [1..N -> 0..M-1]
  /\ \E i \in 1..N : counters[i] = 0

Next ==
  /\ \E i \in 1..N :
      IF i = 1
      THEN counters' = [counters EXCEPT ![i] = (counters[N] + 1) % M]
      ELSE counters' = [counters EXCEPT ![i] = IF counters[i-1] # counters[i] THEN counters[i-1] ELSE counters[i]]

Spec ==
  Init /\ [][Next]_counters

StabilizationInv ==
  \E t \in Nat : <>(\A i, j \in 1..N : counters[i] = counters[j])

THEOREM Spec => []<>StabilizationInv
```