```
MODULE TokenCirculation
EXTENDS Integers, Sequences

CONSTANTS N, K
ASSUME N > 0
ASSUME K > N

VARIABLES counters, tokenHolders

Init ==
  /\ counters \in [1..N -> 0..K-1]
  /\ tokenHolders = {i \in 1..N : i = 1 \/ counters[i] # counters[(i-1) % N + 1]}

Next ==
  (\E i \in 1..N :
    /\ (i = 1 /\ counters[1] < K-1 /\ counters' = [counters EXCEPT ![1] = @ + 1])
    \/ (i # 1 /\ counters[i] # counters[(i-1) % N + 1] /\ counters' = [counters EXCEPT ![i] = counters[(i-1) % N + 1]])
    /\ tokenHolders' = {j \in 1..N : j = 1 \/ counters'[j] # counters'[(j-1) % N + 1]}
  )

Spec ==
  Init /\ [][Next]_counters

TokenExistence ==
  []<>tokenHolders # {}

Liveness ==
  <>[]~(tokenHolders = {1})

Convergence ==
  <>[](Cardinality(tokenHolders) = 1)

THEOREM Spec => []TokenExistence
THEOREM Spec => Liveness
THEOREM Spec => Convergence

Fairness == WF_Next(counters)
```
Note: The above TLA+ specification models the distributed token circulation algorithm on a unidirectional ring of N processes. It ensures that at least one process holds the token, and eventually, exactly one process holds the token. The `Next` action models the asynchronous interleaving of processes, where each process can perform local steps comparing its counter to its neighbor and either incrementing its own counter or copying the predecessor's counter according to the token semantics. The safety properties (`TokenExistence`) and liveness properties (`Liveness` and `Convergence`) are specified using temporal logic operators.