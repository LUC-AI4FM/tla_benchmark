------------------------------- MODULE DiningPhilosophers -------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS N

VARIABLES sem, pc

Init == /\ sem = <<1, 1, 1, 1, 1>>[1..N]
        /\ pc = [p \in {0..N-1} |-> "think"]

Next ==
    LET AcquireForks[p] ==
            \/ /\ p > 0
               /\ pc[p] = "think"
               /\ sem[p] = 1
               /\ sem[(p+1) % N] = 1
               /\ pc' = [pc EXCEPT ![p] = "eat"]
               /\ sem' = [sem EXCEPT ![p] = 0, ![(p+1) % N] = 0]
            \/ /\ p = 0
               /\ pc[p] = "think"
               /\ sem[p] = 1
               /\ sem[N-1] = 1
               /\ pc' = [pc EXCEPT ![p] = "eat"]
               /\ sem' = [sem EXCEPT ![p] = 0, ![N-1] = 0]
        ReleaseForks[p] ==
            \/ /\ pc[p] = "eat"
               /\ pc' = [pc EXCEPT ![p] = "think"]
               /\ sem' = [sem EXCEPT ![p] = 1, ![(p+1) % N] = 1]
    IN
        \E p \in {0..N-1} :
            \/ AcquireForks[p]
            \/ ReleaseForks[p]

Spec ==
    /\ Init
    /\ [][Next]_<<pc>>
    /\ WF_next(<<pc>>)

MutualExclusion == 
    \A p, q \in {0..N-1} : p # q => ~(\E i \in {0, 1} : pc[p] = "eat" /\ pc[(p+i) % N] = "eat")

StarvationFreedom ==
    \A p \in {0..N-1} : [](<>[]pc[p] = "eat"))

=============================================================================