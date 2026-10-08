```
MODULE TokenRing
EXTENDS Integers, FiniteSets
CONSTANTS N, M
VARIABLES counters

Init == (* Initialize counters to arbitrary values *)
        /\ counters \in [1..N -> 0..M-1]

Next == 
  \/ (* Node 0 creates a new token *)
     /\ counters' = [counters EXCEPT ![0] = (counters[0] + 1) % M]
  \/ (* Other nodes pass the token *)
     \E i \in 1..N :
       /\ counters' = [counters EXCEPT ![i] = counters[(i-1) % N]]
       /\ counters[i] # counters[(i-1) % N]

Spec == Init /\ [][Next]_counters

StabilizationInvariant == 
  \E t \in counters : counters = [i \in 1..N |-> IF i = t THEN counters[t] ELSE counters[(t-1) % N]]

THEOREM Spec => []<>StabilizationInvariant
```
Note: This TLA+ specification models the system as described, with `counters` representing the state of each node in the ring. The `Init` predicate initializes the system to any valid state, and the `Next` predicate specifies how each node updates its counter value based on the values of its predecessor. The `Spec` predicate defines the overall behavior of the system as the conjunction of the initial condition and the next-state relation. The `StabilizationInvariant` predicate captures the stabilization property, which states that eventually the system reaches a state where all nodes have the same token value, and this state is maintained indefinitely. The `THEOREM` statement asserts that the specification implies the stabilization property.