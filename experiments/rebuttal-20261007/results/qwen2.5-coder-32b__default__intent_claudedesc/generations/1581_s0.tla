------------------------------- MODULE DiningPhilosophers -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N
ASSUME N \in Nat /\ N > 1

VARIABLES forks, eating

Fork == 0..N-1
Philosopher == 0..N-1

Init == 
    /\ forks = [f \in Fork |-> TRUE]
    /\ eating = [p \in Philosopher |-> FALSE]

PickupRightFirst(p) ==
    \/ p # N-1 -> 
        /\ forks[p] 
        /\ forks[(p+1) % N]
        /\ forks' = [forks EXCEPT ![p] = FALSE, ![p+1] = FALSE]
        /\ eating' = [eating EXCEPT ![p] = TRUE]
    \/ p = N-1 ->
        /\ forks[N-1]
        /\ forks[0]
        /\ forks' = [forks EXCEPT ![N-1] = FALSE, ![0] = FALSE]
        /\ eating' = [eating EXCEPT ![N-1] = TRUE]

PickupLeftFirst(p) ==
    \/ p # 0 -> 
        /\ forks[p]
        /\ forks[(p-1) % N]
        /\ forks' = [forks EXCEPT ![p] = FALSE, ![(p-1) % N] = FALSE]
        /\ eating' = [eating EXCEPT ![p] = TRUE]
    \/ p = 0 ->
        /\ forks[0]
        /\ forks[N-1]
        /\ forks' = [forks EXCEPT ![0] = FALSE, ![N-1] = FALSE]
        /\ eating' = [eating EXCEPT ![0] = TRUE]

PutDown(p) ==
    /\ eating[p]
    /\ forks' = [forks EXCEPT ![p] = TRUE, ![(p+1) % N] = TRUE]
    /\ eating' = [eating EXCEPT ![p] = FALSE]

Next == 
    \/ \E p \in Philosopher \ {N-1} : PickupRightFirst(p)
    \/ PickupLeftFirst(N-1)
    \/ \E p \in Philosopher : PutDown(p)

Spec == 
    /\ Init
    /\ [][Next]_<<forks, eating>>
    /\ WF_next(<<forks, eating>>)

Safety ==
    \A p \in Philosopher :
        ~ (eating[p] /\ eating[(p+1) % N])

Liveness ==
    \A p \in Philosopher : 
        <>[] (eating[p])

THEOREM Spec => []Safety
THEOREM Spec => Liveness

=============================================================================