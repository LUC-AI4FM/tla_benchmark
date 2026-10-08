------------------------------- MODULE DiningPhilosophers -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N \* Number of philosophers

VARIABLES 
    state, \* State of each philosopher: "thinking" or "hungry"
    forkOwner, \* Owner of each fork (philosopher number)
    forkClean \* Cleanliness of each fork: TRUE if clean, FALSE if dirty

Init == /\ state = [p \in 1..N -> "thinking"]
        /\ forkOwner = [f \in 1..N -> f]
        /\ forkClean = [f \in 1..N -> FALSE]

Next ==
    \/ \/ \* Philosopher requests a fork
       \/ \E p \in 1..N : state[p] = "hungry" /\ 
          (\E f \in {p, (p % N) + 1} : forkOwner[f] # p /\ forkClean[f])
    \/ \/ \* Philosopher passes a dirty fork to a neighbor
       \/ \E p \in 1..N : state[p] = "hungry" /\ 
          (\E f \in {p, (p % N) + 1} : forkOwner[f] = p /\ ~forkClean[f])
    \/ \/ \* Philosopher eats and then makes forks dirty
       \/ \E p \in 1..N : state[p] = "hungry" /\ 
          (\A f \in {p, (p % N) + 1} : forkOwner[f] = p /\ forkClean[f])
    \/ \/ \* Philosopher finishes eating and becomes thinking
       \/ \E p \in 1..N : state[p] = "hungry" /\ 
          (\A f \in {p, (p % N) + 1} : forkOwner[f] = p /\ ~forkClean[f])

Spec ==
    /\ Init
    /\ [][Next]_<<state, forkOwner, forkClean>>
    /\ WF_next(<<state, forkOwner, forkClean>>)

TypeOK ==
    /\ state \in [1..N -> {"thinking", "hungry"}]
    /\ forkOwner \in [1..N -> 1..N]
    /\ forkClean \in [1..N -> BOOLEAN]

MutualExclusion ==
    \A f \in 1..N : 
        LET p1 == f
            p2 == (f % N) + 1
        IN \/ state[p1] # "hungry"
           \/ state[p2] # "hungry"

StarvationFreedom ==
    \A p \in 1..N :
        <>[]<>(state[p] = "hungry" /\ 
               (\A f \in {p, (p % N) + 1} : forkOwner[f] = p /\ forkClean[f]))

THEOREM Spec => []TypeOK
THEOREM Spec => []MutualExclusion
THEOREM Spec => StarvationFreedom

=============================================================================