------------------------------- MODULE DiningPhilosophers ------------------------------

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N

VARIABLES pc, sem

Init == 
    /\ pc = <<0>> \o [i \in 1..N -> 0]
    /\ sem = [f \in 0..N-1 -> TRUE]

PickupFork[i] ==
    LET rightFork = i
        leftFork  = (i + 1) % N
    IN
    CASE i /= 0 ->
         /\ pc[i] = 0
         /\ sem[rightFork]
         /\ sem[leftFork]
         /\ sem' = [sem EXCEPT ![rightFork] = FALSE, ![leftFork] = FALSE]
         /\ pc' = [pc EXCEPT ![i] = 1]
     [] i = 0 ->
         /\ pc[i] = 0
         /\ sem[leftFork]
         /\ sem[rightFork]
         /\ sem' = [sem EXCEPT ![rightFork] = FALSE, ![leftFork] = FALSE]
         /\ pc' = [pc EXCEPT ![i] = 1]

Eat[i] ==
    /\ pc[i] = 1
    /\ pc' = [pc EXCEPT ![i] = 2]

PutdownForks[i] ==
    LET rightFork = i
        leftFork  = (i + 1) % N
    IN
    /\ pc[i] = 2
    /\ sem'[rightFork] = TRUE
    /\ sem'[leftFork] = TRUE
    /\ pc' = [pc EXCEPT ![i] = 0]

Next ==
    \/ \E i \in 1..N : PickupFork[i]
    \/ \E i \in 1..N : Eat[i]
    \/ \E i \in 1..N : PutdownForks[i]

Spec == 
    /\ Init
    /\ [][Next]_<<pc, sem>>
    /\ WF_next(<<pc, sem>>)

MutualExclusion ==
    /\ \A i \in 0..N-1 :
        LET leftPhilosopher = (i - 1) % N
            rightPhilosopher = (i + 1) % N
        IN
        ~(\E j \in {leftPhilosopher, rightPhilosopher} : pc[j] = 1 /\ pc[i] = 1)

StarvationFreedom ==
    \/ \A i \in 0..N-1 : WF_next(<<pc[i]>>) /\ <>[]<>(pc'[i] = 1)

=============================================================================