```
MODULE RingAlgorithm
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES x, y, pc

Init ==
  /\ N \in Nat+
  /\ x = [i \in 1..N |-> 0]
  /\ y = [i \in 1..N |-> 0]
  /\ pc = [i \in 1..N |-> "start"]

Next ==
  \/ \E i \in 1..N :
      /\ pc[i] = "start"
      /\ x' = [x EXCEPT ![i] = 1]
      /\ y' = y
      /\ pc' = [pc EXCEPT ![i] = "copy"]
      /\ UNCHANGED <<y, pc>>
  \/ \E i \in 1..N :
      /\ pc[i] = "copy"
      /\ x' = x
      /\ y' = [y EXCEPT ![i] = x[(i-1) % N + 1]]
      /\ pc' = [pc EXCEPT ![i] = "done"]
      /\ UNCHANGED <<x, pc>>

Spec == Init /\ [][Next]_<<x, y, pc>>

Termination == <>(\A i \in 1..N : pc[i] = "done")

Inv == /\ N \in Nat+
        /\ x \in [1..N -> Int]
        /\ y \in [1..N -> Int]
        /\ pc \in [1..N -> {"start", "copy", "done"}]

THEOREM Spec => []Termination
PROOF omitted

THEOREM Spec => [](Termination => \E i \in 1..N : y[i] = 1)
PROOF omitted
```