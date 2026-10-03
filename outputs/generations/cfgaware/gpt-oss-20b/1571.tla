------------------------------ MODULE DiningPhilosophers ------------------------------

EXTENDS Integers

CONSTANT N

VARIABLES forks, state

(* State constants *)
THINKING == 0
FIRST    == 1
EATING   == 2

firstFork(i) ==
    IF i = 0 THEN Mod(i - 1 + N, N)
    ELSE i

secondFork(i) ==
    IF i = 0 THEN i
    ELSE Mod(i - 1 + N, N)

Init ==
    /\ forks = [k \in 0..N-1 |-> TRUE]
    /\ state = [p \in 0..N-1 |-> THINKING]

AcquireFirst(i) ==
    /\ i \in 0..N-1
    /\ state[i] = THINKING
    /\ forks[firstFork(i)] = TRUE
    /\ forks'   = [forks EXCEPT ![firstFork(i)] = FALSE]
    /\ state'   = [state EXCEPT ![i] = FIRST]

AcquireSecond(i) ==
    /\ i \in 0..N-1
    /\ state[i] = FIRST
    /\ forks[secondFork(i)] = TRUE
    /\ forks'   = [forks EXCEPT ![secondFork(i)] = FALSE]
    /\ state'   = [state EXCEPT ![i] = EATING]

Release(i) ==
    /\ i \in 0..N-1
    /\ state[i] = EATING
    /\ forks[firstFork(i)]   = FALSE
    /\ forks[secondFork(i)]  = FALSE
    /\ forks'   = [forks EXCEPT ![firstFork(i)] = TRUE,
                   ![secondFork(i)] = TRUE]
    /\ state'   = [state EXCEPT ![i] = THINKING]

Next == \E i \in 0..N-1 :
          AcquireFirst(i) \/ AcquireSecond(i) \/ Release(i)

Spec == Init /\ [][Next]_<<forks,state>>

Invariant ==
    \A i, j \in 0..N-1 :
        (state[i] = EATING /\ state[j] = EATING) => i = j

===============================================================================