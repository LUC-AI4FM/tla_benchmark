```tla
MODULE RegularRegisters
EXTENDS Integers, FiniteSets

CONSTANTS N

VARIABLES x, y, pc

Init ==
  /\ x = [i \in 0..N-1 |-> {}]
  /\ y = [i \in 0..N-1 |-> 0]
  /\ pc = [i \in 0..N-1 |-> "a1"]

Next ==
  \/ (\E i \in 0..N-1 :
      /\ pc[i] = "a1"
      /\ x' = [x EXCEPT ![i] = {0, 1}]
      /\ y' = y
      /\ pc' = [pc EXCEPT ![i] = "a2"])
  \/ (\E i \in 0..N-1 :
      /\ pc[i] = "a2"
      /\ x' = [x EXCEPT ![i] = {1}]
      /\ y' = y
      /\ pc' = [pc EXCEPT ![i] = "b"])
  \/ (\E i \in 0..N-1 :
      /\ pc[i] = "b"
      /\ \E v \in x[(i-1) % N] : y' = [y EXCEPT ![i] = v]
      /\ x' = x
      /\ pc' = [pc EXCEPT ![i] = "Done"])
  \/ (\A i \in 0..N-1 : pc[i] = "Done" /\ x' = x /\ y' = y /\ pc' = pc)

TypeOK ==
  /\ x \in [0..N-1 -> SUBSET {0, 1}]
  /\ y \in [0..N-1 -> {0, 1}]
  /\ pc \in [0..N-1 -> {"a1", "a2", "b", "Done"}]

Inv ==
  /\ TypeOK
  /\ \A i \in 0..N-1 : pc[i] \in {"b", "Done"} => x[i] = {1}
  /\ \/ \E i \in 0..N-1 : pc[i] /= "Done"
      \/ \E i \in 0..N-1 : y[i] = 1

PCorrect ==
  \A i \in 0..N-1 : pc[i] = "Done" => \E j \in 0..N-1 : y[j] = 1

Termination ==
  <>(\A i \in 0..N-1 : pc[i] = "Done")

Spec == Init /\ [][Next]_<<x, y, pc>> /\ WF_(Next) <<x, y, pc>>

THEOREM Correctness == Spec => []PCorrect
THEOREM Correctness2 == Spec => []Inv

```
Note: The `WF_(Next)` is used to specify weak fairness for the next-state relation. This ensures that if a process is enabled to make a step, it will eventually do so.