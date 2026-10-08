------------------------------ MODULE DiningPhilosophers ------------------------------
EXTENDS Integers

CONSTANTS N
ASSUME N > 0

VARIABLE forkOwners, philosopherState

(* Helper functions *)
leftFork(i)   == i
rightFork(i)  == IF i < N THEN i + 1 ELSE 1
nextPhilo(i)  == IF i < N THEN i + 1 ELSE 1

(* Initial state *)
Init ==
    /\ forkOwners \in [1..N -> 0..N]
    /\ philosopherState \in [1..N -> {"Thinking","Hungry","Eating"}]
    /\ \A f \in 1..N : forkOwners[f] = 0
    /\ \A i \in 1..N : philosopherState[i] = "Thinking"

(* Actions *)
Think(i) ==
    /\ i \in 1..N
    /\ philosopherState[i] = "Thinking"
    /\ philosopherState' = [philosopherState EXCEPT ![i] = "Hungry"]
    /\ forkOwners' = forkOwners

Acquire(i) ==
    /\ i \in 1..N
    /\ philosopherState[i] = "Hungry"
    /\ forkOwners[leftFork(i)] = 0
    /\ forkOwners[rightFork(i)] = 0
    /\ forkOwners' = [forkOwners EXCEPT ![leftFork(i)] = i, ![rightFork(i)] = i]
    /\ philosopherState' = [philosopherState EXCEPT ![i] = "Eating"]

Release(i) ==
    /\ i \in 1..N
    /\ philosopherState[i] = "Eating"
    /\ forkOwners[leftFork(i)] = i
    /\ forkOwners[rightFork(i)] = i
    /\ forkOwners' = [forkOwners EXCEPT ![leftFork(i)] = 0, ![rightFork(i)] = 0]
    /\ philosopherState' = [philosopherState EXCEPT ![i] = "Thinking"]

PhiloAction(i) == Think(i) \/ Acquire(i) \/ Release(i)

Next ==
    \E i \in 1..N : PhiloAction(i)

Spec ==
    Init
    /\ [][Next]_(forkOwners, philosopherState)
    /\ \A i \in 1..N : WF_(PhiloAction(i))

Invariant ==
    (* No two adjacent philosophers eating simultaneously *)
    \A i \in 1..N :
        ~(philosopherState[i] = "Eating" /\ philosopherState[nextPhilo(i)] = "Eating")
    /\ (* If a philosopher is eating, he holds both forks *)
    \A i \in 1..N :
        (philosopherState[i] = "Eating") =>
            (forkOwners[leftFork(i)] = i /\ forkOwners[rightFork(i)] = i)

============================================================================