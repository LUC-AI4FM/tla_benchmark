```
MODULE ConcurrentSystem
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES pc, 
          sharedReg, 
          localState

Init == 
  (pc = [i \in 1..N |-> "start"]) 
  /\ (sharedReg = [i \in 1..N |-> {0}]) 
  /\ (localState = [i \in 1..N |-> 0])

TypeInvariant == 
  pc \in [1..N -> {"start", "write", "read", "terminated"}]
  /\ sharedReg \in [1..N -> SUBSET {0, 1}]
  /\ localState \in [1..N -> {0, 1}]

Next == 
  \/ \E i \in 1..N : 
    (pc[i] = "start") 
    /\ (pc' = [pc EXCEPT ![i] = "write"]) 
    /\ (sharedReg' = sharedReg) 
    /\ (localState' = localState)
  \/ \E i \in 1..N : 
    (pc[i] = "write") 
    /\ (pc' = [pc EXCEPT ![i] = "read"]) 
    /\ (sharedReg' = [sharedReg EXCEPT ![i] = {0, 1}]) 
    /\ (localState' = localState)
  \/ \E i \in 1..N : 
    (pc[i] = "read") 
    /\ (pc' = [pc EXCEPT ![i] = "terminated"]) 
    /\ (sharedReg' = sharedReg) 
    /\ (localState' = [localState EXCEPT ![i] = CHOOSE v \in sharedReg[(i-1)%N + 1] : TRUE])
  \/ \E i \in 1..N : 
    (pc[i] = "read") 
    /\ (pc' = pc) 
    /\ (sharedReg' = [sharedReg EXCEPT ![i] = {0, 1}]) 
    /\ (localState' = localState)

Spec == Init /\ [][Next]_<<pc, sharedReg, localState>>
           /\ WF_<<pc, sharedReg, localState>>(Next)

TerminationSafety == <>[]\A i \in 1..N : pc[i] = "terminated" => \E j \in 1..N : localState[j] = 1

Progress == []<>(\A i \in 1..N : pc[i] = "terminated")

THEOREM Spec => []TerminationSafety
THEOREM Spec => Progress
```
Note: The `CHOOSE` operator is used to model the nondeterministic behavior of reading from a regular register. The `(i-1)%N + 1` expression calculates the index of the left neighbor for process `i`.