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

Next ==
  \/ \E i \in 1..N :
      /\ pc[i] = "start"
      /\ x[i]' = x[i] \cup {1}
      /\ UNCHANGED <<y, pc, done>>
  \/ \E i \in 1..N :
      /\ pc[i] = "write1"
      /\ x[i]' = {1}
      /\ pc'[i] = "read"
      /\ UNCHANGED <<y, done>>
  \/ \E i \in 1..N :
      /\ pc[i] = "read"
      /\ \E v \in x[(i mod N) + 1] : y[i]' = v
      /\ pc'[i] = "done"
      /\ done'[i] = TRUE
      /\ UNCHANGED <<x, done>>

Spec == Init /\ [][Next]_<<x, y, pc, done>>

PCorrect == <>[](\A i \in 1..N : done[i]) => \E i \in 1..N : y[i] = 1

Inv == 
  /\ x \in [1..N -> SUBSET {0, 1}]
  /\ y \in [1..N -> {0, 1}]
  /\ pc \in [1..N -> {"start", "write1", "read", "done"}]
  /\ done \in [1..N -> BOOLEAN]

THEOREM Spec => []PCorrect
PROOF BY induction <<x, y, pc, done>>
  BASE CASE Init => PCorrect
  INDUCTIVE STEP Next => Inv'
  QED

THEOREM Spec => <><>[](\A i \in 1..N : done[i])
PROOF BY fairness <<pc, done>>
  SHOWS (\A i \in 1..N : pc[i] = "done") => (\A i \in 1..N : done[i])
  QED
```