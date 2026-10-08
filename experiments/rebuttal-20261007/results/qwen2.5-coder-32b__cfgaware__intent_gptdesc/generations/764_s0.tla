------------------------------- MODULE DiningPhilosophers -------------------------------

CONSTANTS N \* Number of philosophers, must be >= 2

VARIABLES 
    state, \* State of each philosopher (THINKING | HUNGRY | EATING)
    forkHolder, \* Holder of each fork (philosopher index or NULL if available)
    forkState \* State of each fork (CLEAN | DIRTY)

PHILOSOPHERS == 0 .. N-1
FORKS == 0 .. N-1

\* Initial state: All philosophers are thinking, all forks are clean and available
Init == 
    /\ state = [p \in PHILOSOPHERS |-> THINKING]
    /\ forkHolder = [f \in FORKS |-> NULL]
    /\ forkState = [f \in FORKS |-> CLEAN]

\* Next-state relation
Next ==
    \/ \/ p \in PHILOSOPHERS : ThinkToHungry(p)
       \/ p \in PHILOSOPHERS : EatToThinking(p)
       \/ \/ f \in FORKS : RequestFork(f)
          \/ f \in FORKS : ReleaseFork(f)

\* A philosopher transitions from THINKING to HUNGRY
ThinkToHungry(p) ==
    /\ state[p] = THINKING
    /\ state' = [state EXCEPT ![p] = HUNGRY]
    /\ UNCHANGED forkHolder
    /\ UNCHANGED forkState

\* A philosopher transitions from EATING to THINKING and releases both forks
EatToThinking(p) ==
    /\ state[p] = EATING
    /\ LET leftFork  == (p - 1) % N
       rightFork == p
    IN
        /\ forkHolder[leftFork] = p
        /\ forkHolder[rightFork] = p
        /\ state' = [state EXCEPT ![p] = THINKING]
        /\ forkHolder' = [forkHolder EXCEPT ![leftFork] = NULL, ![rightFork] = NULL]
        /\ forkState' \in [f \in FORKS |-> IF f \in {leftFork, rightFork} THEN ForkStateChange(f) ELSE forkState[f]]

\* A philosopher requests a fork from its neighbor
RequestFork(f) ==
    LET p == (f + 1) % N
        q == f
    IN
        /\ state[p] = HUNGRY
        /\ forkHolder[f] = q
        /\ forkHolder' = [forkHolder EXCEPT ![f] = p]
        /\ forkState' \in [f \in FORKS |-> IF f = f THEN ForkStateChange(f) ELSE forkState[f]]
        /\ UNCHANGED state

\* A philosopher releases a fork to its neighbor
ReleaseFork(f) ==
    LET p == (f + 1) % N
        q == f
    IN
        /\ state[p] \in {HUNGRY, EATING}
        /\ forkHolder[f] = p
        /\ forkHolder' = [forkHolder EXCEPT ![f] = q]
        /\ forkState' \in [f \in FORKS |-> IF f = f THEN ForkStateChange(f) ELSE forkState[f]]
        /\ UNCHANGED state

\* Abstract function to change the state of a fork when it is passed or used
ForkStateChange(f) == CHOOSE s \in {CLEAN, DIRTY} : TRUE

\* Specification
Spec ==
    Init /\ [][Next]_<<state, forkHolder, forkState>>

\* Safety: No two neighboring philosophers may be in the eating state simultaneously
Safety ==
    \/ p \in PHILOSOPHERS :
        LET leftFork  == (p - 1) % N
            rightFork == p
        IN
            /\ state[p] = EATING
            /\ forkHolder[leftFork] = p
            /\ forkHolder[rightFork] = p
            /\ \/ state[(p + 1) % N] \= EATING
               \/ LET leftNeighborLeftFork  == p
                      leftNeighborRightFork == (p + 1) % N
                  IN
                      forkHolder[leftNeighborLeftFork] \= (p + 1) % N
                      \/ forkHolder[leftNeighborRightFork] \= (p + 1) % N

\* Invariants: Forks are always held by exactly one of the two adjacent philosophers; all variables respect their intended types/ranges
Invariants ==
    /\ state \in [PHILOSOPHERS -> {THINKING, HUNGRY, EATING}]
    /\ forkHolder \in [FORKS -> PHILOSOPHERS \cup {NULL}]
    /\ forkState \in [FORKS -> {CLEAN, DIRTY}]
    /\ \/ f \in FORKS :
            LET leftPhilosopher == (f + 1) % N
                rightPhilosopher == f
            IN
                \/ forkHolder[f] = NULL
                \/ forkHolder[f] = leftPhilosopher
                \/ forkHolder[f] = rightPhilosopher

\* Liveness: Under fairness assumptions for philosopher processes, every philosopher who becomes hungry will eventually eat (no starvation)
Liveness ==
    \A p \in PHILOSOPHERS :
        <>[](state[p] = HUNGRY) => <>([]<>(state[p] = EATING))

\* Progress: The system must always be able to make a next step (no global deadlock), assuming the protocol rules and fairness
Progress ==
    \/ Next

=============================================================================