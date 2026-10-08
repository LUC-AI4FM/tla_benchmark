```
MODULE RingAlgorithm
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES x, y, pc

Init == (* Initial condition *)
        /\ x = [i \in 1..N |-> 0]
        /\ y = [i \in 1..N |-> 0]
        /\ pc = [i \in 1..N |-> "start"]

Next == (* Next state relation *)
        \/ \E i \in 1..N :
            pc[i] = "start"
            /\ x' = [x EXCEPT ![i] = 1]
            /\ y' = y
            /\ pc' = [pc EXCEPT ![i] = "copy"]
        \/ \E i \in 1..N :
            pc[i] = "copy"
            /\ x' = x
            /\ y' = [y EXCEPT ![i] = IF i = 1 THEN x[N] ELSE x[(i-1)]]
            /\ pc' = [pc EXCEPT ![i] = "done"]

Spec == Init /\ [][Next]_<<x, y, pc>>

Termination == <>(\A i \in 1..N : pc[i] = "done")

SafetyProperty == 
        (\A i \in 1..N : pc[i] = "done") => \E i \in 1..N : y[i] = 1

Inv == (* Inductive invariant *)
      /\ \A i \in 1..N : x[i] \in {0, 1}
      /\ \A i \in 1..N : y[i] \in {0, 1}
      /\ \A i \in 1..N : pc[i] \in {"start", "copy", "done"}
      /\ (\A i \in 1..N : pc[i] = "done") => \E i \in 1..N : y[i] = 1

THEOREM Spec => []Inv
THEOREM Spec => Termination
THEOREM Spec => SafetyProperty
```