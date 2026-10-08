```
MODULE TerminationDetection
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES active, detected

Init ==
  /\ active \in [1..N -> {True, False}]
  /\ detected = (active = [i \in 1..N |-> FALSE])

Next ==
  \/ (\E i \in 1..N : 
        active[i] = TRUE /\ 
        active' = [active EXCEPT ![i] = FALSE])
  \/ (\E i, j \in 1..N :
        active[i] = TRUE /\ 
        active[j] = FALSE /\ 
        active' = [active EXCEPT ![j] = TRUE])
  \/ (detected' = TRUE /\ detected = FALSE /\ active = [i \in 1..N |-> FALSE])

Spec ==
  Init /\ [][Next]_<<active, detected>>
  WF_(detected' = TRUE /\ detected = FALSE /\ active = [i \in 1..N |-> FALSE])_<<active, detected>>

THEOREM Spec => []~(detected = TRUE /\ \E i \in 1..N : active[i] = TRUE)
THEOREM Spec => [](active = [i \in 1..N |-> FALSE] => []active = [i \in 1..N |-> FALSE])
THEOREM Spec => []((\A i \in 1..N : ~active[i]) => <>detected)
```