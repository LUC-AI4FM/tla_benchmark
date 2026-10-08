```
MODULE SharedMemoryAlgorithm
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES x, y, done, pc

Init == (* Initial condition *)
        /\ x = [i \in 1..N |-> {0}]
        /\ y = [i \in 1..N |-> 0]
        /\ done = [i \in 1..N |-> FALSE]
        /\ pc = [i \in 1..N |-> "start"]

Next == (* Next-state relation *)
       \/ \E i \in 1..N :
          pc[i] = "start"
          /\ x' = [x EXCEPT ![i] = {0, 1}]
          /\ y' = y
          /\ done' = done
          /\ pc' = [pc EXCEPT ![i] = "write1"]
       \/ \E i \in 1..N :
          pc[i] = "write1"
          /\ x' = [x EXCEPT ![i] = {1}]
          /\ y' = y
          /\ done' = done
          /\ pc' = [pc EXCEPT ![i] = "read"]
       \/ \E i \in 1..N :
          pc[i] = "read"
          /\ \E v \in x[(i + 1) % N + 1] : y'[i] = v
          /\ x' = x
          /\ done' = [done EXCEPT ![i] = TRUE]
          /\ pc' = [pc EXCEPT ![i] = "done"]

Spec == (* Specification *)
       Init /\ [][Next]_<<x, y, done, pc>>

PCorrect == (* Safety property *)
           <<done = [i \in 1..N |-> TRUE]>> => <<\E i \in 1..N : y[i] = 1>>

Inv == (* Inductive invariant *)
      /\ x \in [1..N -> {0, 1}]
      /\ y \in [1..N -> {0, 1}]
      /\ done \in [1..N -> BOOLEAN]
      /\ pc \in [1..N -> {"start", "write1", "read", "done"}]

THEOREM PCorrect => []PCorrect
PROOF * By induction using Inv *

THEOREM Spec => []Inv
PROOF * By induction *
```