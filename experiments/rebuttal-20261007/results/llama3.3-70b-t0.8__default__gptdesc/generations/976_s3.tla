```
MODULE RingAlgorithm
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES x, y, pc

Init ==
  /\ N \in Nat+
  /\ x = [i \in 1..N |-> 0]
  /\ y = [i \in 1..N |-> 0]
  /\ pc = [i \in 1..N |-> "Start"]

Next ==
  (\E i \in 1..N :
    /\ pc[i] = "Start"
    /\ x' = [x EXCEPT ![i] = 1]
    /\ y' = y
    /\ pc' = [pc EXCEPT ![i] = "Copy"]
    /\ \A j \in 1..N \ {i} : 
      /\ x'[j] = x[j]
      /\ y'[j] = y[j]
      /\ pc'[j] = pc[j]
  ) \lor
  (\E i \in 1..N :
    /\ pc[i] = "Copy"
    /\ x' = x
    /\ y' = [y EXCEPT ![i] = IF i = 1 THEN x[N] ELSE x[(i-1)]]
    /\ pc' = [pc EXCEPT ![i] = "Done"]
    /\ \A j \in 1..N \ {i} : 
      /\ x'[j] = x[j]
      /\ y'[j] = y[j]
      /\ pc'[j] = pc[j]
  )

Spec ==
  Init /\ [][Next]_<<x, y, pc>>

Inv == 
  /\ N \in Nat+
  /\ pc \in [1..N -> {"Start", "Copy", "Done"}]
  /\ x \in [1..N -> {0, 1}]
  /\ y \in [1..N -> {0, 1}]

THEOREM Spec => []Inv

Termination ==
  <>(\A i \in 1..N : pc[i] = "Done")

THEOREM Spec => Termination

SafetyProperty ==
  (\A i \in 1..N : pc[i] = "Done") => \E j \in 1..N : y[j] = 1

THEOREM Spec => []SafetyProperty
```