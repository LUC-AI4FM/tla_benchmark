```
MODULE TerminationDetection
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES active, pending, detected

Init ==
  /\ active \in [1..N -> BOOLEAN]
  /\ pending \in [1..N -> Nat]
  /\ detected = FALSE
  /\ active = [i \in 1..N |-> TRUE]
  /\ pending = [i \in 1..N |-> 0]

Next ==
  \/ \E i \in 1..N :
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ pending' = pending
    /\ detected' = detected
  \/ \E i \in 1..N :
    /\ active' = active
    /\ pending' = [pending EXCEPT ![i] = pending[i] + 1]
    /\ detected' = detected
  \/ \E i \in 1..N :
    /\ active' = active
    /\ pending' = [pending EXCEPT ![i] = pending[i] - 1]
    /\ pending[i] > 0
    /\ detected' = detected
  \/ DetectTermination

DetectTermination ==
  /\ ~detected
  /\ \A i \in 1..N : ~active[i]
  /\ \A i \in 1..N : pending[i] = 0
  /\ detected' = TRUE
  /\ UNCHANGED active
  /\ UNCHANGED pending

Spec == Init /\ [][Next]_<<active, pending, detected>>
WeakFairness == WF_(DetectTermination)

THEOREM Spec => []detected => []\A i \in 1..N : ~active[i] /\ pending[i] = 0
THEOREM Spec => [](detected => []detected)
THEOREM Spec => []<><detectTermination>_detected
THEOREM Spec => [](\A i \in 1..N : ~active[i] /\ pending[i] = 0) => <>(detected' = TRUE)

INVARIANT active \in [1..N -> BOOLEAN]
INVARIANT pending \in [1..N -> Nat]
INVARIANT detected \in BOOLEAN
INVARIANT \A i \in 1..N : pending[i] >= 0
```
Note: `UNCHANGED` is used to specify that a variable does not change, and `WF_` specifies weak fairness. The `_` symbol after `Next` and `DetectTermination` specifies the variables that are changed by these actions.