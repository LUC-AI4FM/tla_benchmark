```tla
MODULE DiningPhilosophers

EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES forks, states, hungry, eating

Init ==
  /\ forks \in [1..N -> {1, 2}]  \* Each fork is initially held by one of two adjacent philosophers (arbitrarily chosen)
  /\ states \in [1..N -> {"thinking", "hungry", "eating"}]
  /\ hungry \in [1..N -> BOOLEAN]
  /\ eating \in [1..N -> BOOLEAN]
  /\ forks = [i \in 1..N |-> IF i mod 2 = 0 THEN i ELSE (i + 1) % N + 1]  \* Initialize fork holders
  /\ states = [i \in 1..N |-> "thinking"]  \* All philosophers start thinking
  /\ hungry = [i \in 1..N |-> FALSE]
  /\ eating = [i \in 1..N |-> FALSE]

Next ==
  \/ \E i \in 1..N :
    /\ states[i] = "thinking"
    /\ states' = [states EXCEPT ![i] = "hungry"]
    /\ hungry' = [hungry EXCEPT ![i] = TRUE]
    /\ forks' = forks
    /\ eating' = eating
  \/ \E i \in 1..N :
    /\ states[i] = "hungry"
    /\ \A j \in {i % N + 1, (i + 1) % N + 1} : states[j] # "eating"  \* Check neighboring philosophers are not eating
    /\ forks' = [forks EXCEPT ![i] = i]
    /\ states' = [states EXCEPT ![i] = "eating"]
    /\ hungry' = [hungry EXCEPT ![i] = FALSE]
    /\ eating' = [eating EXCEPT ![i] = TRUE]
  \/ \E i \in 1..N :
    /\ states[i] = "eating"
    /\ forks' = [forks EXCEPT ![i] = (i + 1) % N + 1]
    /\ states' = [states EXCEPT ![i] = "thinking"]
    /\ hungry' = hungry
    /\ eating' = [eating EXCEPT ![i] = FALSE]

Spec ==
  Init /\ [][Next]_<<forks, states, hungry, eating>>

SafetyInv ==
  /\ \A i \in 1..N : forks[i] \in {i, (i + 1) % N + 1}
  /\ \A i, j \in 1..N : i # j => forks[i] # forks[j]
  /\ \A i \in 1..N : states[i] \in {"thinking", "hungry", "eating"}
  /\ \A i \in 1..N : hungry[i] \/ eating[i] => states[i] = "hungry" \/ states[i] = "eating"
  /\ \A i, j \in 1..N : (i % N + 1 = j) \/ ((i + 1) % N + 1 = j) => ~(states[i] = "eating" /\ states[j] = "eating")

LivenessInv ==
  WF_<<forks, states, hungry, eating>>(Next)

THEOREM Spec => []SafetyInv
THEOREM Spec => LivenessInv

```
Note: This TLA+ specification models the dining philosophers problem with N concurrent philosophers. The `Init` predicate defines the initial state of the system, where each fork is held by one philosopher and all philosophers are thinking. The `Next` predicate describes the possible next states of the system, including a philosopher becoming hungry, eating, or thinking. The `Spec` predicate defines the complete specification as the conjunction of the initial state and the next-state relation. The `SafetyInv` predicate specifies the safety properties, including mutual exclusion on shared forks and type invariants. The `LivenessInv` predicate specifies the liveness property using the weak fairness operator (`WF_`).