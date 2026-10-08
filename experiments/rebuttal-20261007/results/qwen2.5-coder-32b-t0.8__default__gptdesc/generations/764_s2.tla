```tla
MODULE DiningPhilosophers

EXTENDS TLC, Integers, Sequences, FiniteSets

CONSTANTS N

VARIABLES sem, pc

ASSUME N \in Nat /\ N > 1

Init == 
    /\ sem = <<TRUE>> ^ N
    /\ pc = <<0>> ^ N

AcquireForks[i \in {0..N-1}] ==
    LET right = i
        left  = (i - 1) % N
        order = IF i = 0 THEN <<left, right>> ELSE <<right, left>>
    IN
        /\ sem[order[1]] = TRUE
        /\ sem' = [sem EXCEPT ![order[1]] = FALSE]
        /\ pc' = [pc EXCEPT ![i] = 1]

AcquireSecondFork[i \in {0..N-1}] ==
    LET right = i
        left  = (i - 1) % N
        order = IF i = 0 THEN <<left, right>> ELSE <<right, left>>
    IN
        /\ sem[order[2]] = TRUE
        /\ sem' = [sem EXCEPT ![order[2]] = FALSE]
        /\ pc' = [pc EXCEPT ![i] = 2]

Eat[i \in {0..N-1}] ==
    /\ pc[i] = 2
    /\ pc' = [pc EXCEPT ![i] = 3]

ReleaseForks[i \in {0..N-1}] ==
    LET right = i
        left  = (i - 1) % N
    IN
        /\ sem[right] = FALSE
        /\ sem[left] = FALSE
        /\ sem' = [sem EXCEPT ![right] = TRUE, ![left] = TRUE]
        /\ pc' = [pc EXCEPT ![i] = 0]

Next ==
    \/ \E i \in {0..N-1} : pc[i] = 0 /\ AcquireForks[i]
    \/ \E i \in {0..N-1} : pc[i] = 1 /\ AcquireSecondFork[i]
    \/ \E i \in {0..N-1} : pc[i] = 2 /\ Eat[i]
    \/ \E i \in {0..N-1} : pc[i] = 3 /\ ReleaseForks[i]

Spec ==
    Init /\ [][Next]_<<pc, sem>> /\ WF_next(<<pc>>) 

MutualExclusion == 
    \A i, j \in {0..N-1} : i # j => ~(\E k \in {0, 2} : pc[i] = k /\ pc[j] = k)

StarvationFreedom ==
    \A i \in {0..N-1} : [](<>[]pc[i] = 3))

Theorem == Spec /\ MutualExclusion /\ StarvationFreedom
```