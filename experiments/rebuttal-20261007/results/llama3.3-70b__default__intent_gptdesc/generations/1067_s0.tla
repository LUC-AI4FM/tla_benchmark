```
MODULE DistributedTerminationDetection
EXTENDS Integers, Sequences

CONSTANTS N
VARIABLES states, terminated

states == << <<
  \* An array of boolean values representing the state (active/inactive) of each process
>>
>>
terminated == FALSE

Init ==
  /\ states \in [1..N -> {TRUE, FALSE}]
  /\ terminated = FALSE

LocalTermination(p) ==
  /\ states[p] = TRUE
  /\ states' = [states EXCEPT ![p] = FALSE]
  /\ terminated' = terminated

ActivateProcess(p, q) ==
  /\ p \in 1..N
  /\ q \in 1..N
  /\ p # q
  /\ states[q] = FALSE
  /\ states' = [states EXCEPT ![q] = TRUE]
  /\ terminated' = terminated

DetectTermination ==
  /\ ~terminated
  /\ terminated' = TRUE
  /\ \A p \in 1..N : states[p] = FALSE
  /\ states' = states

Next ==
  \/ \E p \in 1..N : LocalTermination(p)
  \/ \E p \in 1..N : \E q \in 1..N : ActivateProcess(p, q)
  \/ DetectTermination

Spec == Init /\ [][Next]_<<states, terminated>>

Quiescent == \A p \in 1..N : ~states[p]

SafetyInvariant ==
  terminated => Quiescent

QuiescencePersistence ==
  []<>(Quiescent => []Quiescent)

LivenessProperty ==
  <>Quiescent => <>(terminated = TRUE)

THEOREM Spec => []SafetyInvariant
THEOREM Spec => QuiescencePersistence
THEOREM Spec => LivenessProperty
```