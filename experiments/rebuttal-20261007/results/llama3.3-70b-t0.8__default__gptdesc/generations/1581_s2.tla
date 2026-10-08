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
    /\ pc' = [pc EXCEPT ![i] = "hungry"]
    /\ sem' = sem
  \/ \E i \in 1..N :
    /\ pc[i] = "hungry"
    /\ (i # 1) => sem[i]
    /\ (i = 1) => sem[N]
    /\ pc' = [pc EXCEPT ![i] = "eat"]
    /\ sem' = [sem EXCEPT ![i] = FALSE, ![(i + N - 1) % N + 1] = FALSE]
  \/ \E i \in 1..N :
    /\ pc[i] = "eat"
    /\ pc' = [pc EXCEPT ![i] = "think"]
    /\ sem' = [sem EXCEPT ![i] = TRUE, ![(i + N - 1) % N + 1] = TRUE]

Spec ==
  /\ Init
  /\ [][Next]_<<pc, sem>>
  /\ WF_vars(<<pc, sem>>)(\E i \in 1..N : pc[i] = "hungry" /\ (i # 1) => sem[i] /\ (i = 1) => sem[N])
  /\ WF_vars(<<pc, sem>>)(\E i \in 1..N : pc[i] = "eat")
  /\ []<>(\A i \in 1..N : pc[i] = "eat")

THEOREM Spec => []<>~( \E i \in 1..N-1 : pc[i] = "eat" /\ pc[i + 1] = "eat")
```