```
MODULE DijkstraTokenRing
EXTENDS Integers, FiniteSets

CONSTANTS N, M
ASSUME N <= M + 1

VARIABLES counters

Init ==
  /\ counters \in [1..N -> 0..M]

Next ==
  \/ \E i \in 1..N :
      IF i = 1
      THEN IF counters[1] = counters[N]
           THEN counters' = [counters EXCEPT ![1] = (counters[1] + 1) % M]
           ELSE counters' = [counters EXCEPT ![1] = counters[N]]
      ELSE IF counters[i] # counters[i-1]
           THEN counters' = [counters EXCEPT ![i] = counters[i-1]]
           ELSE counters' = counters
  /\ UNCHANGED << >>

Spec ==
  Init /\ [][Next]_counters

StabilizationInvariant ==
  \E t \in 0..M :
    (\A i, j \in 1..N : 
       (counters[i] = t) /\ (counters[j] = counters[1]) \/ 
       (counters[i] # t) /\ (counters[j] = counters[N]))

StabilizationProperty ==
  <>(\A i \in 1..N :
      IF i <= 1
      THEN counters[i] = counters[1]
      ELSE counters[i] = counters[N])

THEOREM Spec => []StabilizationInvariant
THEOREM Spec => StabilizationProperty

Fairness ==
  WF_vars(Next, counters)

TLADEF StabilizationTheorem == Spec => StabilizationProperty
```
Note: The above TLA+ specification uses the `UNCHANGED` operator to specify that all variables not explicitly mentioned in a transition remain unchanged. It also uses the `WF_vars` operator from the `Fairness` module (not shown) to express weak fairness on all transitions.