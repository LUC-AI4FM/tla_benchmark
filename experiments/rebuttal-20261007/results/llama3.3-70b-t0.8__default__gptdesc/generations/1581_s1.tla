```
MODULE DiningPhilosophers
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES pc, sem

Init ==
  /\ pc = [i \in 0..N-1 |-> "thinking"]
  /\ sem = [i \in 0..N-1 |-> TRUE]

Next ==
  \/ \E i \in 0..N-1 :
    /\ pc[i] = "thinking"
    /\ (i # 0) => sem[(i + 1) % N]
    /\ (i = 0) => sem[0]
    /\ pc' = [pc EXCEPT ![i] = "hungry"]
    /\ sem' = sem
  \/ \E i \in 0..N-1 :
    /\ pc[i] = "hungry"
    /\ ((i # 0) => (sem[(i + N - 1) % N] /\ sem[(i + 1) % N])
           \/ (i = 0) => (sem[N-1] /\ sem[0]))
    /\ pc' = [pc EXCEPT ![i] = "eating"]
    /\ sem' = [sem EXCEPT ![(i + N - 1) % N] = FALSE, !(i % N) = FALSE]
  \/ \E i \in 0..N-1 :
    /\ pc[i] = "eating"
    /\ pc' = [pc EXCEPT ![i] = "thinking"]
    /\ sem' = [sem EXCEPT ![(i + N - 1) % N] = TRUE, !(i % N) = TRUE]

Spec == Init /\ [][Next]_<<pc, sem>>
           /\ WF_<<pc, sem>>(\E i \in 0..N-1 : pc[i] = "thinking" /\ (i # 0) => sem[(i + 1) % N])
           /\ WF_<<pc, sem>>(\E i \in 0..N-1 : pc[i] = "hungry")
           /\ SF_<<pc, sem>>(\E i \in 0..N-1 : pc[i] = "eating")

Invariant == \A i \in 0..N-2 : ~(pc[i] = "eating" /\ pc[(i + 1) % N] = "eating")
StarvationFreedom == \A i \in 0..N-1 : []<>(pc[i] = "eating")
THEOREM Spec => []Invariant
THEOREM Spec => StarvationFreedom
```