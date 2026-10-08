------------------------------- MODULE DiningPhilosophers -------------------------------
CONSTANTS N

VARIABLES 
    \* forks[i] = (owner, clean), where owner is the philosopher holding the fork and clean is a boolean indicating if the fork is clean
    forks,
    \* states[i] = state of philosopher i, where state is either "thinking" or "hungry"
    states

\* Initial predicate: each fork starts with its lower-numbered neighbor and is dirty
Init == 
    /\ forks = <<<<i \in 1..N-1 -> [owner |-> i, clean |-> FALSE], [owner |-> N, clean |-> FALSE]>>>
    /\ states = <<<<i \in 1..N -> "thinking">>>

\* Action: philosopher i requests a fork from its neighbor j
RequestFork(i, j) ==
    /\ states[i] = "hungry"
    /\ forks[j].owner # i
    /\ \/ (j = i + 1) \/ (i = N \and j = 1)
    /\ \/ ~forks[j].clean
       \/ (forks[j].clean /\ forks[j].owner = j)

\* Action: philosopher i passes a fork to its neighbor j
PassFork(i, j) ==
    /\ states[i] = "hungry"
    /\ forks[i].owner = i
    /\ forks[j].owner # i
    /\ \/ (j = i + 1) \/ (i = N \and j = 1)
    /\ ~forks[j].clean

\* Action: philosopher i eats if it holds both adjacent forks and they are clean
Eat(i) ==
    /\ states[i] = "hungry"
    /\ forks[i].owner = i
    /\ forks[IF i = N THEN 1 ELSE i + 1].owner = i
    /\ forks[i].clean
    /\ forks[IF i = N THEN 1 ELSE i + 1].clean

\* Action: philosopher i finishes eating and makes both adjacent forks dirty
FinishEating(i) ==
    /\ states[i] = "hungry"
    /\ forks[i].owner = i
    /\ forks[IF i = N THEN 1 ELSE i + 1].owner = i
    /\ forks[i].clean
    /\ forks[IF i = N THEN 1 ELSE i + 1].clean

\* Next state relation
Next ==
    \/ \E i, j \in 1..N : RequestFork(i, j) /\ forks' = [forks EXCEPT ![j] = [owner |-> i, clean |-> forks[j].clean]] /\ states' = states
    \/ \E i, j \in 1..N : PassFork(i, j) /\ forks' = [forks EXCEPT ![i] = [owner |-> j, clean |-> FALSE], ![j] = [owner |-> j, clean |-> TRUE]] /\ states' = states
    \/ \E i \in 1..N : Eat(i) /\ states' = [states EXCEPT ![i] = "thinking"] /\ forks' = forks
    \/ \E i \in 1..N : FinishEating(i) /\ states' = [states EXCEPT ![i] = "hungry"] /\ forks' = [forks EXCEPT ![i] = [owner |-> i, clean |-> FALSE], ![IF i = N THEN 1 ELSE i + 1] = [owner |-> IF i = N THEN 1 ELSE i + 1, clean |-> FALSE]]

\* Specification
Spec ==
    Init /\ [][Next]_<<forks, states>>

\* Type correctness invariant
TypeOK ==
    /\ \A i \in 1..N : forks[i].owner \in 1..N
    /\ \A i \in 1..N : forks[i].clean \in BOOLEAN
    /\ \A i \in 1..N : states[i] \in {"thinking", "hungry"}

\* Mutual exclusion invariant: no two adjacent philosophers can eat simultaneously
MutualExclusion ==
    \A i \in 1..N : ~(\E j \in {IF i = N THEN 1 ELSE i + 1, IF i = 1 THEN N ELSE i - 1} : states[i] = "hungry" /\ states[j] = "hungry")

\* Liveness property: every philosopher must eat infinitely often
StarvationFreedom ==
    \A i \in 1..N : [](states[i] = "hungry") ~> <>(states[i] = "thinking")

=============================================================================