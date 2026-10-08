```
MODULE TokenRing
EXTENDS Integers, FiniteSets

CONSTANTS N, M
ASSUME N > 0 && M > 1

VARIABLES counters, source

Init ==
  /\ counters \in [1..N -> 0..M-1]
  /\ source = 1

Next ==
  \/ \E i \in 1..N :
    /\ i = source
    /\ counters' = [counters EXCEPT ![i] = (counters[i] + 1) % M]
    /\ source' = source
  \/ \E i \in 2..N :
    /\ counters' = [counters EXCEPT ![i] = counters[(i-1)]
    /\ source' = source
  \/ \E i \in 1..N :
    /\ i = 1
    /\ counters' = [counters EXCEPT ![i] = counters[N]
    /\ source' = source

Spec ==
  Init /\ [][Next]_<<counters, source>>
 WF_source(inject) == <>(source = 1 /\ Next)
SF_pass(i \in 2..N) == [](<> (counters[i] /= counters[(i-1)] /\ Next))
Fairness == WF_source(inject) /\ \A i \in 2..N : SF_pass(i)

SafetyInv ==
  \A i \in 1..N : counters[i] \in 0..M-1

SelfStabilization ==
  <>(\E v \in 0..M-1 :
    /\ \E i, j \in 1..N :
      (counters[i] = v /\ counters[j] = (v-1) % M)
      \/ (counters[i] = (v-1) % M /\ counters[j] = v)
    /\ \A k \in 1..N : 
      (counters[k] = v) \/ (counters[k] = (v-1) % M)
  )

THEOREM Spec => []SafetyInv
THEOREM Spec => SelfStabilization

```
Note: This TLA+ specification models the distributed stabilizing token-ring algorithm as described. It includes the initial state, next-state relation, safety invariant, self-stabilization property, and fairness constraints to ensure that the token creation and passing actions cannot be indefinitely postponed. The `THEOREM` statements assert that the specification implies the desired safety and liveness properties.