```
MODULE RingAlgorithm
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES x, y, pc

Init ==
  /\ x = [i \in 1..N |-> 0]
  /\ y = [i \in 1..N |-> 0]
  /\ pc = [i \in 1..N |-> "Start"]

Next ==
  /\ \E i \in 1..N :
      /\ pc[i] = "Start"
      /\ x' = [x EXCEPT ![i] = 1]
      /\ y' = y
      /\ pc' = [pc EXCEPT ![i] = "Copy"]
  \/ \E i \in 1..N :
      /\ pc[i] = "Copy"
      /\ x' = x
      /\ y' = [y EXCEPT ![i] = x[(i-1 # N) + 1]]
      /\ pc' = [pc EXCEPT ![i] = "Done"]
  \/ \E i \in 1..N :
      /\ pc[i] = "Done"
      /\ x' = x
      /\ y' = y
      /\ pc' = pc

Spec == Init /\ [][Next]_<x, y, pc>

Termination == <>(\A i \in 1..N : pc[i] = "Done")

SafetyProperty == []<>(\A i \in 1..N : pc[i] = "Done" => \E j \in 1..N : y[j] = 1)

Inv == /\ x \in [1..N -> 0..1]
      /\ y \in [1..N -> 0..1]
      /\ pc \in [1..N -> {"Start", "Copy", "Done"}]

THEOREM Spec => []Termination
PROOF OMITTED

THEOREM Spec => []SafetyProperty
PROOF OMITTED

TYPECORRECTNESS CONSTRAINTS
  N \in Nat
  x \in [1..N -> Int]
  y \in [1..N -> Int]
  pc \in [1..N -> String]
```
Note: The `PROOF OMITTED` statements indicate that the proofs for these theorems are not provided here. In a real-world scenario, you would need to provide the actual proofs using TLAPS or another proof assistant.