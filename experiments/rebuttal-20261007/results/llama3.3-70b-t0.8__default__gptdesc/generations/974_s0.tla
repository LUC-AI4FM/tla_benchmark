```
MODULE SharedMemoryAlgorithm
EXTENDS Integers, Sequences

CONSTANTS N
VARIABLES x, y, done, temp

Init ==
  /\ x = [i \in 1..N |-> {0}]
  /\ y = [i \in 1..N |-> 0]
  /\ done = [i \in 1..N |-> FALSE]
  /\ temp = [i \in 1..N |-> 0]

Next ==
  \/ \E i \in 1..N :
    /\ ~done[i]
    /\ x[i] = {0}
    /\ x' = [x EXCEPT ![i] = {0, 1}]
    /\ UNCHANGED <<y, done, temp>>
  \/ \E i \in 1..N :
    /\ ~done[i]
    /\ x[i] = {0, 1}
    /\ x' = [x EXCEPT ![i] = {1}]
    /\ UNCHANGED <<y, done, temp>>
  \/ \E i \in 1..N :
    /\ ~done[i]
    /\ x[i] = {1}
    /\ temp' = [temp EXCEPT ![i] = CHOOSE v \in x[(i % N) + 1] : TRUE]
    /\ UNCHANGED <<x, y, done>>
  \/ \E i \in 1..N :
    /\ ~done[i]
    /\ temp[i] # 0
    /\ y' = [y EXCEPT ![i] = temp[i]]
    /\ done' = [done EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<x, temp>>

Spec == Init /\ [][Next]_<<x, y, done, temp>>

PCorrect == <>[](\A i \in 1..N : done[i] => \E j \in 1..N : y[j] = 1)

Inv == /\ x \in [1..N -> SUBSET Int]
      /\ y \in [1..N -> Int]
      /\ done \in [1..N -> Bool]
      /\ temp \in [1..N -> Int]

THEOREM Spec => []PCorrect
PROOF BY induction <<x, y, done, temp>>
  BASE CASE Init => PCorrect
  INDUCTIVE STEP Next => PCorrect'
END PROOF

THEOREM Spec => Inv
PROOF BY induction <<x, y, done, temp>>
  BASE CASE Init => Inv
  INDUCTIVE STEP Next => Inv'
END PROOF
```