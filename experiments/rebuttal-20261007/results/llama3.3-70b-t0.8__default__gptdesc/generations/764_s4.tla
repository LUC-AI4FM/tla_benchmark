```
MODULE DiningPhilosophers
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES sem, pc

Init == (* Initial state *)
        /\ sem = <<1, 1, ..., 1>>  \* Initialize all forks as available
        /\ pc = [i \in 1..N |-> "think"]  \* All philosophers start thinking

Next == (* Next-state relation *)
        \/ \E i \in 1..N :  \* Some philosopher takes a step
            (pc[i] = "think"  \* Philosopher is thinking
             /\ pc' = [pc EXCEPT ![i] = "hungry"]
             /\ sem' = sem)
         \/ \E i \in 1..N :  \* Philosopher picks up right fork (1 through N-1) or left fork (0)
            ((i # 0  \* 1 through N-1
              /\ pc[i] = "hungry"
              /\ sem[(i - 1) % N + 1] = 1
              /\ pc' = [pc EXCEPT ![i] = "rightFork"]
              /\ sem' = [sem EXCEPT ![(i - 1) % N + 1] = 0])
             \/
             (i = 0  \* Philosopher 0
              /\ pc[i] = "hungry"
              /\ sem[N] = 1
              /\ pc' = [pc EXCEPT ![i] = "leftFork"]
              /\ sem' = [sem EXCEPT ![N] = 0]))
         \/ \E i \in 1..N :  \* Philosopher picks up left fork (1 through N-1) or right fork (0)
            ((i # 0
              /\ pc[i] = "rightFork"
              /\ sem[i] = 1
              /\ pc' = [pc EXCEPT ![i] = "eating"]
              /\ sem' = [sem EXCEPT ![i] = 0])
             \/
             (i = 0
              /\ pc[i] = "leftFork"
              /\ sem[1] = 1
              /\ pc' = [pc EXCEPT ![i] = "eating"]
              /\ sem' = [sem EXCEPT ![1] = 0]))
         \/ \E i \in 1..N :  \* Philosopher finishes eating and puts down both forks
            (pc[i] = "eating"
             /\ pc' = [pc EXCEPT ![i] = "think"]
             /\ sem' = [sem EXCEPT ![i] = 1, ![(i - 1) % N + 1] = 1])

Spec == Init /\ [][Next]_<<sem, pc>>
Invariant == \A i, j \in 1..N :  \* Mutual exclusion invariant
                 (i # j  \* Two adjacent philosophers can't eat at the same time
                  => ~(pc[i] = "eating" /\ pc[j] = "eating"))

Fairness == <>[]<>[Next]_<<sem, pc>>  \* Strong fairness for each process

StarvationFreedom == []<> \A i \in 1..N : <>(pc[i] = "eating")  \* Every philosopher eats infinitely often
```