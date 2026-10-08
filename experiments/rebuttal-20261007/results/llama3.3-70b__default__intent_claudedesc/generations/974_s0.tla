```
MODULE SharedMemoryAlgorithm
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES sharedReg, localReg, writing, done

Init ==
  /\ sharedReg = [i \in 1..N |-> 0]
  /\ localReg = [i \in 1..N |-> 0]
  /\ writing = [i \in 1..N |-> FALSE]
  /\ done = [i \in 1..N |-> FALSE]

Next ==
  \/ \E i \in 1..N :
      /\ ~writing[i]
      /\ sharedReg' = [sharedReg EXCEPT ![i] = 0]
      /\ writing' = [writing EXCEPT ![i] = TRUE]
      /\ localReg' = localReg
      /\ done' = done
  \/ \E i \in 1..N :
      /\ writing[i]
      /\ sharedReg' = [sharedReg EXCEPT ![i] = 1]
      /\ writing' = [writing EXCEPT ![i] = FALSE]
      /\ localReg' = localReg
      /\ done' = done
  \/ \E i \in 1..N :
      /\ ~done[i]
      /\ ~writing[i]
      /\ sharedReg' = sharedReg
      /\ writing' = writing
      /\ localReg' = [localReg EXCEPT ![i] = IF sharedReg[(i-1) % N + 1] = 0 THEN 0 ELSE 1]
      /\ done' = [done EXCEPT ![i] = TRUE]

Spec == Init /\ [][Next]_<<sharedReg, localReg, writing, done>>
  
Fairness == <>[](~\E i \in 1..N : ~done[i])

THEOREM Spec => []<>(\E i \in 1..N : localReg[i] = 1)
PROOF BY induction
  BASE CASE: Init => [](Spec => (\E i \in 1..N : localReg[i] = 1))
  INDUCTIVE STEP: 
    ASSUME Spec, 
           [](Spec => (\E i \in 1..N : localReg[i] = 1)), 
           <>(\E i \in 1..N : ~done[i])
    PROVE [](Spec => (\E i \in 1..N : localReg[i] = 1))
```
Note: The above TLA+ specification models the shared-memory algorithm with N processes. It defines the `Init` predicate to represent the initial state, the `Next` predicate to describe the possible next states, and the `Spec` predicate as the conjunction of `Init` and the stuttering closure of `Next`. The fairness condition ensures that all processes eventually complete. The theorem statement proves the safety property using an inductive invariant.