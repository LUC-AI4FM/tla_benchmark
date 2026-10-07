------------------------------- MODULE DiningPhilosophers -------------------------------
EXTENDS Naturals, TLC

CONSTANTS NP \* Number of Philosophers
ASSUME NP = 5

VARIABLES forks, philosophers

vars == <<forks, philosophers>>

Init ==
    /\ forks = [f \in 1..NP -> [holder: (f-1) % NP + 1, clean: FALSE]]
    /\ forks[2].holder = 1
    /\ philosophers = [p \in 1..NP -> hungry]

Next ==
    LET leftFork[p] == (p - 1) % NP + 1
        rightFork[p] == p
        canEat[p] == 
            \/ /\ forks[leftFork[p]].holder = p
               /\ forks[rightFork[p]].holder = p
               /\ forks[leftFork[p]].clean
               /\ forks[rightFork[p]].clean
    IN
    \E p \in 1..NP :
        \/ /\ philosophers[p] = "Loop"
           /\ (forks[leftFork[p]].holder = p /\ ~forks[leftFork[p]].clean)
              -> (\* Clean and pass left fork *)
                 forks' = [forks EXCEPT ![leftFork[p]] = 
                    [holder |-> (p - 2) % NP + 1, clean |-> TRUE]]
           \/ (forks[rightFork[p]].holder = p /\ ~forks[rightFork[p]].clean)
              -> (\* Clean and pass right fork *)
                 forks' = [forks EXCEPT ![rightFork[p]] = 
                    [holder |-> (p % NP) + 1, clean |-> TRUE]]
           \/ canEat[p]
              -> (\* Eat if possible *)
                 philosophers' = [philosophers EXCEPT ![p] = "Eating"]
                 forks' = [forks EXCEPT ![leftFork[p]].clean = FALSE,
                                             ![rightFork[p]].clean = FALSE]
        \/ /\ philosophers[p] = "Eating"
           -> (\* Finish eating *)
              philosophers' = [philosophers EXCEPT ![p] = "Think"]
        \/ /\ philosophers[p] = "Think"
           -> (\* Think and become hungry again *)
              philosophers' = [philosophers EXCEPT ![p] = "Loop"]

Spec ==
    /\ Init
    /\ [][Next]_<<forks, philosophers>>
    /\ WF_<<forks, philosophers>>[UNION { {p \in 1..NP |-> "Loop"} }]

TypeOK ==
    /\ forks \in [1..NP -> [holder: 1..NP, clean: BOOLEAN]]
    /\ philosophers \in [1..NP -> {"Loop", "Eating", "Think"}]

ExclusiveAccess ==
    \A p \in 1..NP :
        philosophers[p] = "Eating"
        => philosophers[(p - 1) % NP + 1] # "Eating"

NobodyStarves ==
    \A p \in 1..NP : 
        <>[] (philosophers[p] = "Eating")

=============================================================================