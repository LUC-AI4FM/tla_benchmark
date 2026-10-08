------------------------------- MODULE DiningPhilosophers -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N
ASSUME N \in Nat /\ N > 1

VARIABLES pc, sem

Init == 
    /\ pc = [i \in 0..N-1 |-> "think"]
    /\ sem = [f \in 0..N-1 |-> TRUE]

PickupForks(i) ==
    LET rightFork == i
        leftFork  == (i - 1) % N
    IN
        IF i = 0 THEN
            /\ sem[rightFork]
            /\ sem[leftFork]
            /\ sem' = [sem EXCEPT ![rightFork] = FALSE, ![leftFork] = FALSE]
            /\ pc' = [pc EXCEPT ![i] = "eat"]
        ELSE
            /\ sem[rightFork]
            /\ sem[leftFork]
            /\ sem' = [sem EXCEPT ![rightFork] = FALSE, ![leftFork] = FALSE]
            /\ pc' = [pc EXCEPT ![i] = "eat"]

PutDownForks(i) ==
    LET rightFork == i
        leftFork  == (i - 1) % N
    IN
        /\ sem[rightFork] = FALSE
        /\ sem[leftFork] = FALSE
        /\ sem' = [sem EXCEPT ![rightFork] = TRUE, ![leftFork] = TRUE]
        /\ pc' = [pc EXCEPT ![i] = "think"]

Next ==
    \E i \in 0..N-1 :
        \/ /\ pc[i] = "think"
           /\ pc' = [pc EXCEPT ![i] = "pickup"]
        \/ /\ pc[i] = "pickup"
           /\ PickupForks(i)
        \/ /\ pc[i] = "eat"
           /\ PutDownForks(i)

Spec ==
    /\ Init
    /\ [][Next]_<<pc, sem>>
    /\ WF_<<pc, sem>>(Next)

MutualExclusion ==
    \A i \in 0..N-1 :
        LET rightNeighbor == (i + 1) % N
            leftNeighbor  == (i - 1) % N
        IN
            ~(\E j \in {rightNeighbor, leftNeighbor} : pc[j] = "eat" /\ pc[i] = "eat")

StarvationFreedom ==
    \A i \in 0..N-1 :
        [](<>[]pc[i] = "eat"))

=============================================================================