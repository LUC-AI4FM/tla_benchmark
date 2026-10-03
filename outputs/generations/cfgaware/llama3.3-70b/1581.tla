```
---------------------------- MODULE DiningPhilosophers ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

VARIABLE pc, sem

Init == (* Initial state *)
        /\ pc = [i \in 0..N-1 |-> "think"]
        /\ sem = [i \in 0..N-1 |-> TRUE]

Think(i) == (* Philosopher i is thinking *)
           pc[i] = "think"
           /\ pc' = [pc EXCEPT ![i] = "hungry"]
           /\ sem' = sem

HungryRight(i) == (* Philosopher i picks up right fork *)
                  pc[i] = "hungry"
                  /\ i # 0
                  /\ sem[(i+1) % N]
                  /\ pc' = [pc EXCEPT ![i] = "right"]
                  /\ sem' = [sem EXCEPT ![(i+1) % N] = FALSE]

HungryLeft(i) == (* Philosopher i picks up left fork *)
                 pc[i] = "hungry"
                 /\ i = 0
                 /\ sem[i]
                 /\ pc' = [pc EXCEPT ![i] = "left"]
                 /\ sem' = [sem EXCEPT ![i] = FALSE]

EatRight(i) == (* Philosopher i picks up left fork and eats *)
               pc[i] = "right"
               /\ i # 0
               /\ sem[i]
               /\ pc' = [pc EXCEPT ![i] = "eat"]
               /\ sem' = [sem EXCEPT ![i] = FALSE]

EatLeft(i) == (* Philosopher i picks up right fork and eats *)
              pc[i] = "left"
              /\ i = 0
              /\ sem[(i+1) % N]
              /\ pc' = [pc EXCEPT ![i] = "eat"]
              /\ sem' = [sem EXCEPT ![(i+1) % N] = FALSE]

Done(i) == (* Philosopher i finishes eating *)
          pc[i] = "eat"
          /\ pc' = [pc EXCEPT ![i] = "think"]
          /\ sem' = [sem EXCEPT ![i] = TRUE, ![(i+1) % N] = TRUE]

Next == (* Global next-state relation *)
        \E i \in 0..N-1 : 
          (Think(i))
          \/ (HungryRight(i))
          \/ (HungryLeft(i))
          \/ (EatRight(i))
          \/ (EatLeft(i))
          \/ (Done(i))

Spec == Init /\ [][Next]_<<pc, sem>>
        /\ \A i \in 0..N-1 : WF_vars(Next, <<pc, sem>>)

Invariant == (* Mutual-exclusion style safety invariant *)
             \A i \in 0..N-1 : pc[i] # "eat" \/ pc[(i+1) % N] # "eat"

StarvationFree == (* Starvation-freedom property *)
                   \A i \in 0..N-1 : []<>pc[i] = "eat"
```