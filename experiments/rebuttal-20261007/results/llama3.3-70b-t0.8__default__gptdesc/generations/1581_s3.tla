```
MODULE DiningPhilosophers
EXTENDS Integers, Sequences

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
      /\ (i # 1)
      /\ pc[i] = "right"
      /\ sem[i]
      /\ pc' = [pc EXCEPT ![i] = "eat"]
      /\ sem' = [sem EXCEPT ![i] = FALSE, ![(i + N - 1) % N + 1] = FALSE]
  \/ \E i \in 1..N :
      /\ (i = 1)
      /\ pc[i] = "think"
      /\ sem[i]
      /\ pc' = [pc EXCEPT ![i] = "left"]
      /\ sem' = [sem EXCEPT ![i] = FALSE]
  \/ \E i \in 1..N :
      /\ (i = 1)
      /\ pc[i] = "left"
      /\ sem[(i + N - 1) % N + 1]
      /\ pc' = [pc EXCEPT ![i] = "eat"]
      /\ sem' = [sem EXCEPT ![(i + N - 1) % N + 1] = FALSE]
  \/ \E i \in 1..N :
      /\ pc[i] = "eat"
      /\ pc' = [pc EXCEPT ![i] = "think"]
      /\ sem' = [sem EXCEPT ![i] = TRUE, ![(i + N - 1) % N + 1] = TRUE]

Spec ==
  Init /\ [][Next]_<<pc, sem>>
  /\ WF_<<pc, sem>>(\E i \in 1..N : pc[i] = "think" /\ sem[(i + N - 1) % N + 1])
  /\ WF_<<pc, sem>>(\E i \in 2..N : pc[i] = "right" /\ sem[i])
  /\ WF_<<pc, sem>>(\E i \in 1..N : pc[i] = "eat")
  /\ []<>[i \in 1..N |-> pc[i] = "eat"]

THEOREM Spec => []<>(\A i \in 1..N : pc[i] # "eat" \/ pc[(i + N - 1) % N + 1] # "eat")
```