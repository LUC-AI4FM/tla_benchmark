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
    /\ pc' = [pc EXCEPT ![i] = "wait_left"]
    /\ sem' = sem
  \/ \E i \in 1..N :
    /\ pc[i] = "wait_left"
    /\ i # 1
    /\ sem[i]
    /\ pc' = [pc EXCEPT ![i] = "eat"]
    /\ sem' = [sem EXCEPT ![i] = FALSE]
  \/ \E i \in 1..N :
    /\ pc[i] = "wait_left"
    /\ i = 1
    /\ sem[(i + N - 1) % N + 1]
    /\ pc' = [pc EXCEPT ![i] = "eat"]
    /\ sem' = [sem EXCEPT ![(i + N - 1) % N + 1] = FALSE]
  \/ \E i \in 1..N :
    /\ pc[i] = "eat"
    /\ pc' = [pc EXCEPT ![i] = "wait_right"]
    /\ sem' = sem
  \/ \E i \in 1..N :
    /\ pc[i] = "wait_right"
    /\ sem[(i + N - 1) % N + 1]
    /\ pc' = [pc EXCEPT ![i] = "think"]
    /\ sem' = [sem EXCEPT ![(i + N - 1) % N + 1] = TRUE]
  \/ \E i \in 1..N :
    /\ pc[i] = "wait_right"
    /\ i # 1
    /\ sem[i]
    /\ pc' = [pc EXCEPT ![i] = "think"]
    /\ sem' = [sem EXCEPT ![i] = TRUE]

Spec ==
  /\ Init
  /\ [][Next]_<<pc, sem>>
  /\ WF_<<pc, sem>>(Next)

SafetyInvariant ==
  \A i \in 1..N : pc[i] # "eat" \/ pc[(i + N - 1) % N + 1] # "eat"

StarvationFreedom ==
  \A i \in 1..N : <>[]<>(pc[i] = "eat")

THEOREM Spec => []SafetyInvariant
THEOREM Spec => StarvationFreedom
```