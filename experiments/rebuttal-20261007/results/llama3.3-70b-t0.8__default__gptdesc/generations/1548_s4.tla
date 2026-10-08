```
MODULE OneStepConsensus
EXTENDS Integers, FiniteSets

CONSTANTS N, F, T
VARIABLES sent, received, faulty, state

Init == 
  (sent = [i \in 1..N |-> 0]) /\ 
  (received = [i \in 1..N |-> {}]) /\ 
  (faulty = {}) /\ 
  ((\A i \in 1..N : state[i] = 0) \/ (\A i \in 1..N : state[i] = 1))

TypeOK == 
  sent \in [1..N -> Nat] /\ 
  received \in [1..N -> SUBSET 1..N] /\ 
  faulty \in SUBSET 1..N /\ 
  state \in [1..N -> {0, 1}]

Propose(i) == 
  (sent' = [sent EXCEPT ![i] = sent[i] + 1]) /\ 
  (received' = received) /\ 
  (faulty' = faulty) /\ 
  (state' = state)

Receive(i, j) == 
  (sent' = sent) /\ 
  (received' = [received EXCEPT ![j] = received[j] \cup {i}]) /\ 
  (faulty' = faulty) /\ 
  (state' = state)

Decide(i, v) == 
  (sent' = sent) /\ 
  (received' = received) /\ 
  (faulty' = faulty) /\ 
  (state' = [state EXCEPT ![i] = v])

BecomeFaulty(i) == 
  (sent' = sent) /\ 
  (received' = received) /\ 
  (faulty' = faulty \cup {i}) /\ 
  (state' = state)

Next == 
  (\E i \in 1..N : Propose(i)) \/ 
  (\E i, j \in 1..N : Receive(i, j)) \/ 
  (\E i \in 1..N, v \in {0, 1} : Decide(i, v)) \/ 
  (\E i \in 1..N : BecomeFaulty(i))

Spec == Init /\ [][Next]_<<sent, received, faulty, state>>
  
SafetyInv == TypeOK /\ 
  (\A i \in 1..N : Card(received[i]) <= N - 1) /\ 
  (Card(faulty) <= F) /\ 
  ((\A i \in 1..N : state[i] = 0) \/ (\A i \in 1..N : state[i] = 1))

WF_Step == WF(Next)

THEOREM Spec => []SafetyInv
THEOREM Spec => WF_Step
```
Note: This TLA+ specification uses the `TLA+` syntax and grammar as defined by Leslie Lamport. The model is intended for use with the TLC model checker or other tools that support TLA+.