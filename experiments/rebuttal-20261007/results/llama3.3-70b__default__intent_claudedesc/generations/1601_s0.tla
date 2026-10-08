```
MODULE FischerMutualExclusion
EXTENDS Integers, FiniteSets

CONSTANTS N, Delta, Epsilon
VARIABLES lock, timers, inCS

Init ==
  /\ lock = 0
  /\ timers = [i \in 1..N |-> 0]
  /\ inCS = {}

Next ==
  \/ (\E i \in 1..N :
      /\ lock = 0
      /\ timers[i] = 0
      /\ lock' = i
      /\ timers' = [timers EXCEPT ![i] = Delta]
      /\ inCS' = inCS)
  \/ (\E i \in 1..N :
      /\ lock = i
      /\ timers[i] = Delta
      /\ timers' = [timers EXCEPT ![i] = Epsilon]
      /\ inCS' = {i}
      /\ lock' = lock)
  \/ (\E i \in 1..N :
      /\ lock = i
      /\ timers[i] = Epsilon
      /\ timers' = [timers EXCEPT ![i] = 0]
      /\ inCS' = {}
      /\ lock' = 0)
  \/ (\A i \in 1..N : timers[i] > 0
      /\ timers' = [i \in 1..N |-> timers[i] - 1]
      /\ lock' = lock
      /\ inCS' = inCS)

Spec ==
  Init /\ [][Next]_<<lock, timers, inCS>>

MutualExclusion ==
  \A i, j \in 1..N : i # j => ~(inCS[i] /\ inCS[j])

Liveness ==
  <><i \in 1..N : inCS[i]

THEOREM Spec => []MutualExclusion
THEOREM Spec => Liveness

Fairness == 
  WF_Vars(Next, <<lock, timers, inCS>>)
```