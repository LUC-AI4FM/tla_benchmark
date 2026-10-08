```
MODULE AsyncInterface
EXTENDS Integers, FiniteSets
CONSTANTS DataValues
VARIABLES data, ready, acknowledge

Init ==
  /\ data \in DataValues
  /\ ready \in {0, 1}
  /\ acknowledge \in {0, 1}
  /\ ready = acknowledge

Next ==
  \/ (ready = acknowledge
      /\ data' \in DataValues
      /\ ready' = 1 - ready
      /\ acknowledge' = acknowledge)
  \/ (ready # acknowledge
      /\ data' = data
      /\ ready' = ready
      /\ acknowledge' = ready)
  \/ (data' = data
      /\ ready' = ready
      /\ acknowledge' = acknowledge)

Spec ==
  Init /\ [][Next]_<<data, ready, acknowledge>>

TypeInvariant ==
  /\ data \in DataValues
  /\ ready \in {0, 1}
  /\ acknowledge \in {0, 1}

THEOREM Spec => []TypeInvariant
```