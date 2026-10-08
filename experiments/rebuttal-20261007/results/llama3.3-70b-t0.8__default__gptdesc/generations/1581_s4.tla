```
MODULE DiningPhilosophers
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES pc, sem

Init == (* Initial state *)
        /\ pc = [i \in 1..N |-> "thinking"]
        /\ sem = [i \in 1..N |-> TRUE]

Next == (* Next-state relation *)
        \E i \in 1..N :
          (pc[i] = "thinking") /\
          (pc' = [pc EXCEPT ![i] = "hungry"])
       \/ 
          (pc[i] = "hungry") /\
          ((i # 1) => (sem' = [sem EXCEPT ![i] = FALSE])) /\ 
          (pc' = [pc EXCEPT ![i] = "right_fork_picked"]) 
       \/ 
          (pc[i] = "hungry") /\
          (i = 1) /\
          (sem' = [sem EXCEPT ![N] = FALSE]) /\ 
          (pc' = [pc EXCEPT ![i] = "left_fork_picked"])
       \/ 
          (pc[i] = "right_fork_picked") /\
          (sem[i-1] = TRUE) /\ 
          (sem' = [sem EXCEPT ![i-1] = FALSE]) /\ 
          (pc' = [pc EXCEPT ![i] = "eating"])
       \/ 
          (pc[i] = "left_fork_picked") /\
          (sem[i] = TRUE) /\ 
          (sem' = [sem EXCEPT ![i] = FALSE]) /\ 
          (pc' = [pc EXCEPT ![i] = "eating"])
       \/ 
          (pc[i] = "eating") /\
          (sem' = [sem EXCEPT ![i-1] = TRUE, ![i] = TRUE]) /\ 
          (pc' = [pc EXCEPT ![i] = "thinking"])

Spec == Init /\ [][Next]_<pc>

THEOREM Spec => []<>(\A i \in 1..N : pc[i] = "eating")
THEOREM Spec => \A i \in 1..N : <>[]<>(pc[i] = "eating")

Inv == (* Mutual-exclusion safety invariant *)
      \A i \in 1..N-1 : ~(pc[i] = "eating") \/ ~(pc[i+1] = "eating")
THEOREM Spec => []Inv
```