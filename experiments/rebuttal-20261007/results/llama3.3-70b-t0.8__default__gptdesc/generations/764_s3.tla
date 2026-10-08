```
MODULE DiningPhilosophers
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES sem, pc

Init == (* Initial state *)
        /\ sem = <<1, 1, ..., 1>>  \* Initialize all forks as available
        /\ pc = <<0, 0, ..., 0>>    \* All philosophers start thinking

Next == (* Next-state relation *)
        \/ \E i \in (1..N-1) :
            /\ pc[i] = 0             \* Philosopher i is thinking
            /\ sem[i] = 1            \* Right fork of philosopher i is available
            /\ sem[(i+1) % N] = 1    \* Left fork of philosopher i is available (circular array)
            /\ pc' = [pc EXCEPT ![i] = 2]  \* Move to state where right fork is picked up
            /\ sem' = [sem EXCEPT ![i] = 0, ![(i+1) % N] = 0]
        \/ \E i \in (1..N-1) :
            /\ pc[i] = 2             \* Philosopher i has right fork
            /\ sem[(i+1) % N] = 0    \* Left fork of philosopher i is not available yet
            /\ pc' = [pc EXCEPT ![i] = 3]  \* Move to state where eating
            /\ sem' = sem
        \/ \E i \in (1..N-1) :
            /\ pc[i] = 3             \* Philosopher i is eating
            /\ pc' = [pc EXCEPT ![i] = 0]  \* Move back to thinking state
            /\ sem' = [sem EXCEPT ![i] = 1, ![(i+1) % N] = 1]
        \/ pc[0] = 0                 \* Philosopher 0 is thinking
          /\ sem[N-1] = 1           \* Left fork of philosopher 0 is available (circular array)
          /\ sem[0] = 1             \* Right fork of philosopher 0 is available
          /\ pc' = [pc EXCEPT ![0] = 2]
          /\ sem' = [sem EXCEPT ![N-1] = 0, ![0] = 0]
        \/ pc[0] = 2                 \* Philosopher 0 has left fork
          /\ sem[0] = 0             \* Right fork of philosopher 0 is not available yet
          /\ pc' = [pc EXCEPT ![0] = 3]
          /\ sem' = sem
        \/ pc[0] = 3                 \* Philosopher 0 is eating
          /\ pc' = [pc EXCEPT ![0] = 0]
          /\ sem' = [sem EXCEPT ![N-1] = 1, ![0] = 1]

Spec == Init /\ [][Next]_<<sem, pc>>
 
Fairness == \A i \in (0..N-1) : WF_Var(Next, <<sem, pc>>, i)
StarvationFreedom == \A i \in (0..N-1) : []<>pc[i] = 3

THEOREM Spec => []StarvationFreedom
```
Note: This module should be saved with a `.tla` extension and can be checked using the TLC model checker.