```
MODULE DiningPhilosophers
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES sem, pc

Init ==
  /\ sem = <<1, 1, ..., 1>>  \* Initialize all forks as available
  /\ pc = [i \in 1..N |-> "thinking"]  \* All philosophers start thinking

Next ==
  \/ \E i \in 1..N :
    /\ pc[i] = "thinking"
    /\ sem[(i-1) % N + 1] = 1
    /\ (i = 0 => sem[i] = 1)
    /\ pc' = [pc EXCEPT ![i] = "eating"]
    /\ sem' = [sem EXCEPT ![(i-1) % N + 1] = 0]
    /\ (i = 0 => sem' = [sem' EXCEPT ![i] = 0])
  \/ \E i \in 1..N :
    /\ pc[i] = "eating"
    /\ pc' = [pc EXCEPT ![i] = "thinking"]
    /\ sem' = [sem EXCEPT ![(i-1) % N + 1] = 1]
    /\ (i = 0 => sem' = [sem' EXCEPT ![i] = 1])

Spec == Init /\ [][Next]_<<sem, pc>>

Fairness == \A i \in 1..N : WF(Next, <<sem, pc>>)

StarvationFreedom == \A i \in 1..N : []<>pc[i] = "eating"

MutualExclusion == \A i \in 1..N : pc[i] = "eating" => pc[(i-1) % N + 1] # "eating"
```