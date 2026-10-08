---------------------------- MODULE DiningPhilosophers ----------------------------

CONSTANTS N \* Number of philosophers

ASSUME N \in Nat /\ N > 1

VARIABLES forks, eating

\* Forks are modeled as binary semaphores: TRUE means available, FALSE means taken
Init == 
    /\ forks = [i \in 1..N -> TRUE]
    /\ eating = [i \in 1..N -> FALSE]

\* Acquire a fork if it is available
AcquireFork(phil, fork) ==
    \/ /\ fork = "right"
       /\ forks[phil] 
       /\ forks[phil]' = FALSE
    \/ /\ fork = "left"
       /\ forks[(phil \mod N) + 1]
       /\ forks[(phil \mod N) + 1]' = FALSE

\* Release a fork
ReleaseFork(phil, fork) ==
    \/ /\ fork = "right"
       /\ forks[phil] 
       /\ forks[phil]' = TRUE
    \/ /\ fork = "left"
       /\ forks[(phil \mod N) + 1]
       /\ forks[(phil \mod N) + 1]' = TRUE

\* Action for a philosopher to pick up forks and eat
PickUpAndEat(phil) ==
    IF phil # N 
    THEN \/ /\ AcquireFork(phil, "right")
           /\ AcquireFork(phil, "left")
           /\ eating' = [eating EXCEPT ![phil] = TRUE]
    ELSE \/ /\ AcquireFork(phil, "left")
           /\ AcquireFork(phil, "right")
           /\ eating' = [eating EXCEPT ![phil] = TRUE]

\* Action for a philosopher to release forks after eating
ReleaseForks(phil) ==
    /\ ReleaseFork(phil, "right")
    /\ ReleaseFork(phil, "left")
    /\ eating' = [eating EXCEPT ![phil] = FALSE]

\* Next state relation
Next == 
    \E phil \in 1..N :
        \/ /\ PickUpAndEat(phil)
        \/ /\ eating[phil]
           /\ ReleaseForks(phil)

Spec == Init /\ [][Next]_<<forks, eating>>

\* Safety property: no two adjacent philosophers eat simultaneously
Invariant ==
    \A phil \in 1..N :
        ~ (eating[phil] /\ eating[(phil \mod N) + 1])

\* Liveness property: every philosopher eats infinitely often
StarvationFree ==
    \A phil \in 1..N : 
        <>[] (/\ eating[phil]
              /\ \/ PickUpAndEat(phil)
                 \/ ReleaseForks(phil))

===============================================================================