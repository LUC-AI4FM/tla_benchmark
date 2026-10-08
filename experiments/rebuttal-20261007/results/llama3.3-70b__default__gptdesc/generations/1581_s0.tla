```
MODULE DiningPhilosophers
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES pc, sem

Init ==
  /\ pc = [i \in 1..N |-> "think"]
  /\ sem = [i \in 1..N |-> TRUE]

Next ==
  \/ \E i \in 1..N :
    /\ pc[i] = "think"
    /\ sem[(i + N - 1) % N + 1]
    /\ pc' = [pc EXCEPT ![i] = "right"]
    /\ sem' = sem
  \/ \E i \in 1..N :
    /\ pc[i] = "right"
    /\ (i # 1) => sem[i]
    /\ (i = 1) => sem[N]
    /\ pc' = [pc EXCEPT ![i] = "left"]
    /\ sem' = [sem EXCEPT ![i] = FALSE]
  \/ \E i \in 1..N :
    /\ pc[i] = "left"
    /\ sem[(i + N - 1) % N + 1] = FALSE
    /\ pc' = [pc EXCEPT ![i] = "eat"]
    /\ sem' = sem
  \/ \E i \in 1..N :
    /\ pc[i] = "eat"
    /\ pc' = [pc EXCEPT ![i] = "think"]
    /\ sem' = [sem EXCEPT ![(i + N - 1) % N + 1] = TRUE, ![i] = TRUE]

Spec ==
  Init /\ [][Next]_<<pc, sem>>
  /\ WF_<<pc, sem>>(\E i \in 1..N : pc[i] = "think" /\ sem[(i + N - 1) % N + 1])
  /\ WF_<<pc, sem>>(\E i \in 1..N : pc[i] = "right" /\ (i # 1 => sem[i]) /\ (i = 1 => sem[N]))
  /\ WF_<<pc, sem>>(\E i \in 1..N : pc[i] = "left" /\ sem[(i + N - 1) % N + 1] = FALSE)
  /\ WF_<<pc, sem>>(\E i \in 1..N : pc[i] = "eat")

THEOREM Spec => []~( \E i \in 1..N-1 : pc[i] = "eat" /\ pc[(i+1)%N + 1] = "eat")
THEOREM Spec => \A i \in 1..N : <>[]<>(pc[i] = "eat")

```