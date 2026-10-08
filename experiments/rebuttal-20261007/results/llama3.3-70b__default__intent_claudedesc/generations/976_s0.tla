```
MODULE SimpleConcurrentAlgorithm
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES sharedArray1, sharedArray2, pc

Init ==
  /\ sharedArray1 = [i \in 0..N-1 |-> 0]
  /\ sharedArray2 = [i \in 0..N-1 |-> 0]
  /\ pc = [i \in 0..N-1 |-> "start"]

Next ==
  \/ \E i \in 0..N-1 :
      /\ pc[i] = "start"
      /\ sharedArray1' = [sharedArray1 EXCEPT ![i] = 1]
      /\ sharedArray2' = sharedArray2
      /\ pc' = [pc EXCEPT ![i] = "read"]
  \/ \E i \in 0..N-1 :
      /\ pc[i] = "read"
      /\ sharedArray1' = sharedArray1
      /\ sharedArray2' = [sharedArray2 EXCEPT ![i] = sharedArray1[(i-1) % N]]
      /\ pc' = [pc EXCEPT ![i] = "done"]

Spec ==
  Init /\ [][Next]_<<sharedArray1, sharedArray2, pc>>

TypeInvariant ==
  /\ sharedArray1 \in [0..N-1 -> {0, 1}]
  /\ sharedArray2 \in [0..N-1 -> {0, 1}]
  /\ pc \in [0..N-1 -> {"start", "read", "done"}]

InductiveInvariant ==
  TypeInvariant
  /\ \A i \in 0..N-1 : pc[i] = "done" => sharedArray2[i] = 1 \/ \E j \in 0..N-1 : sharedArray2[j] = 1

Postcondition ==
  \A i \in 0..N-1 : pc[i] = "done" => \E j \in 0..N-1 : sharedArray2[j] = 1

THEOREM Spec => []Postcondition
PROOF OMITTED

THEOREM Spec => WF_<<sharedArray1, sharedArray2, pc>>(Next)
PROOF OMITTED
```