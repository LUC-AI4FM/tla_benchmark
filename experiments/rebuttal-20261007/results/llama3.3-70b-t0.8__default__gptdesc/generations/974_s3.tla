```
MODULE SharedMemoryAlgorithm
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES x, y, pc, done

Init ==
  /\ x = [i \in 1..N |-> {0}]
  /\ y = [i \in 1..N |-> 0]
  /\ pc = [i \in 1..N |-> "start"]
  /\ done = [i \in 1..N |-> FALSE]

Write(i, v) ==
  /\ pc[i] = "write"
  /\ x[i]' = x[i] \cup {v}
  /\ y' = y
  /\ pc' = [pc EXCEPT ![i] = "read"]
  /\ done' = done

Read(i) ==
  /\ pc[i] = "read"
  /\ y'[i] \in x[(i mod N) + 1]
  /\ x' = x
  /\ pc' = [pc EXCEPT ![i] = "done"]
  /\ done' = [done EXCEPT ![i] = TRUE]

Next ==
  \/ \E i \in 1..N : Write(i, 1)
  \/ \E i \in 1..N : Read(i)

Spec == Init /\ [][Next]_<<x, y, pc, done>>

PCorrect == <>(\A i \in 1..N : done[i]) => <>(\E i \in 1..N : y[i] = 1)

Inv ==
  /\ x \in [1..N -> SUBSET Int]
  /\ y \in [1..N -> Int]
  /\ pc \in [1..N -> {"start", "write", "read", "done"}]
  /\ done \in [1..N -> BOOLEAN]

THEOREM Spec => []PCorrect
PROOF OMITTED

THEOREM Spec => <<Inv>>_x
PROOF OMITTED
```