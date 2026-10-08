---------------------------- MODULE DiningPhilosophers ----------------------------

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N \* Number of philosophers

VARIABLES pc, sem \* pc[i] is the state (0: thinking, 1: hungry, 2: eating) of philosopher i; sem[f] is availability of fork f

Init == /\ pc = <<0>>^N
        /\ sem = [f \in 0..(N-1) |-> TRUE]

AcquireForks(i) ==
    \/ /\ pc[i] = 1
       /\ (i # 0 => /\ sem[i] = TRUE
                     /\ sem[(i-1)%N] = TRUE)
       /\ (i = 0 => /\ sem[0] = TRUE
                     /\ sem[N-1] = TRUE)
       /\ \E pc' \in SUBSET {0, 1, 2}: [pc EXCEPT ![i] = 2]
          /\ \E sem' \in SUBSET [f \in 0..(N-1) |-> BOOLEAN]: [sem EXCEPT ![i] = FALSE, ![i-1]%N = FALSE]

ReleaseForks(i) ==
    \/ pc[i] = 2
       /\ \E pc' \in SUBSET {0, 1, 2}: [pc EXCEPT ![i] = 0]
          /\ \E sem' \in SUBSET [f \in 0..(N-1) |-> BOOLEAN]: [sem EXCEPT ![i] = TRUE, ![i-1]%N = TRUE]

Philosopher(i) ==
    \/ pc[i] = 0
       /\ \E pc' \in SUBSET {0, 1, 2}: [pc EXCEPT ![i] = 1]
    \/ AcquireForks(i)
    \/ ReleaseForks(i)

Next == \E i \in 0..(N-1): Philosopher(i)

Spec ==
    /\ Init
    /\ [][Next]_<<pc, sem>>
    /\ WF_<<pc, sem>>(S \in 0..(N-1) |-> Philosopher(S))

MutualExclusion == \A i \in 0..(N-1): \A j \in {i-1}%N, (i+1)%N: ~(\A s \in StateSet: pc[s][i] = 2 /\ pc[s][j] = 2)

StarvationFreedom ==
    \A p \in 0..(N-1):
        [](<>[]<pc[p] = 2>_<<pc, sem>>))

THEOREM Spec => []MutualExclusion
THEOREM Spec => StarvationFreedom

=============================================================================