MODULE DiningPhilosophers
EXTENDS Naturals, Sequences

CONSTANT N

VARIABLES pc, sem

THINKING == 0
HUNGRY_RIGHT == 1
HUNGRY_LEFT == 2
EATING == 3

Right(i) == (i + 1) MOD N

Init ==
    /\ pc = [i \in 0..N-1 |-> THINKING]
    /\ sem = [i \in 0..N-1 |-> TRUE]

AcquireRight(i) ==
    /\ i \in 1..N-1
    /\ pc[i] = THINKING
    /\ sem[i] = TRUE
    /\ sem' = [sem EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = HUNGRY_RIGHT]

AcquireLeft(i) ==
    /\ i \in 1..N-1
    /\ pc[i] = HUNGRY_RIGHT
    /\ sem[Right(i)] = TRUE
    /\ sem' = [sem EXCEPT ![Right(i)] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = EATING]

ReleaseForks(i) ==
    /\ i \in 1..N-1
    /\ pc[i] = EATING
    /\ sem' = [sem EXCEPT ![i] = TRUE, ![Right(i)] = TRUE]
    /\ pc' = [pc EXCEPT ![i] = THINKING]

AcquireLeft0 ==
    /\ pc[0] = THINKING
    /\ sem[0] = TRUE
    /\ sem' = [sem EXCEPT ![0] = FALSE]
    /\ pc' = [pc EXCEPT ![0] = HUNGRY_LEFT]

AcquireRight0 ==
    /\ pc[0] = HUNGRY_LEFT
    /\ sem[Right(0)] = TRUE
    /\ sem' = [sem EXCEPT ![Right(0)] = FALSE]
    /\ pc' = [pc EXCEPT ![0] = EATING]

ReleaseForks0 ==
    /\ pc[0] = EATING
    /\ sem' = [sem EXCEPT ![0] = TRUE, ![Right(0)] = TRUE]
    /\ pc' = [pc EXCEPT ![0] = THINKING]

Next ==
    \/ \E i \in 1..N-1 : AcquireRight(i)
    \/ \E i \in 1..N-1 : AcquireLeft(i)
    \/ \E i \in 1..N-1 : ReleaseForks(i)
    \/ AcquireLeft0
    \/ AcquireRight0
    \/ ReleaseForks0

Inv ==
    \A i \in 0..N-1 :
        ~(pc[i] = EATING /\ pc[Right(i)] = EATING)

StarvationFreedom ==
    \A i \in 0..N-1 : []<>(pc[i] = EATING)

Spec == Init /\ [][Next]_(pc, sem) & Inv & StarvationFreedom & StrongFairness(Next)

============================================================================