```tla
MODULE SharedMemoryAlgorithm

EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES x, y, pc

Init ==
  /\ x = [i \in 1..N |-> {0}]
  /\ y = [i \in 1..N |-> 0]
  /\ pc = [i \in 1..N |-> "start"]

Next ==
  \/ \E i \in 1..N :
      /\ pc[i] = "start"
      /\ x' = [x EXCEPT ![i] = {0, 1}]
      /\ y' = y
      /\ pc' = [pc EXCEPT ![i] = "write1"]
  \/ \E i \in 1..N :
      /\ pc[i] = "write1"
      /\ x' = [x EXCEPT ![i] = {1}]
      /\ y' = y
      /\ pc' = [pc EXCEPT ![i] = "read"]
  \/ \E i \in 1..N :
      /\ pc[i] = "read"
      /\ \E v \in x[(i mod N) + 1] : 
          y' = [y EXCEPT ![i] = v]
      /\ x' = x
      /\ pc' = [pc EXCEPT ![i] = "done"]
  \/ \E i \in 1..N :
      /\ pc[i] = "done"
      /\ x' = x
      /\ y' = y
      /\ pc' = pc

Spec == Init /\ [][Next]_<<x, y, pc>>

PCorrect == <>[]\A i \in 1..N : pc[i] = "done" => \E i \in 1..N : y[i] = 1

Inv ==
  /\ \A i \in 1..N : pc[i] \in {"start", "write1", "read", "done"}
  /\ \A i \in 1..N : x[i] \subseteq {0, 1}
  /\ \A i \in 1..N : y[i] \in {0, 1}

THEOREM Spec => []PCorrect
PROOF BY induction, INVARIANCE OF Inv, PCorrect

THEOREM Spec => <><>[]\A i \in 1..N : pc[i] = "done"
PROOF BY fairness, INVARIANCE OF Inv, Spec
```