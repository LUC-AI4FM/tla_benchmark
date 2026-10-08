MODULE DiningPhilosophers
EXTENDS Naturals

CONSTANTS N, Special

(* Helper functions *)
Left(i) == IF i > 1 THEN i-1 ELSE N
Right(i) == IF i < N THEN i+1 ELSE 1

VARIABLES forks, state

NoAdjacentEating ==
    \A i ∈ 1..N : ~(state[i] = "eating" /\ state[Right(i)] = "eating")

Init ==
    forks = [j ∈ 1..N |-> 0] /\
    state = [i ∈ 1..N |-> "thinking"]

AcquireFirstNonSpecial(i) ==
    /\ i # Special
    /\ state[i] = "thinking"
    /\ forks[Right(i)] = 0
    /\ forks' = [forks EXCEPT ![Right(i)] = 1]
    /\ state' = [state EXCEPT ![i] = "right_acquired"]

AcquireFirstSpecial(i) ==
    /\ i = Special
    /\ state[i] = "thinking"
    /\ forks[Left(i)] = 0
    /\ forks' = [forks EXCEPT ![Left(i)] = 1]
    /\ state' = [state EXCEPT ![i] = "left_acquired"]

AcquireSecondNonSpecial(i) ==
    /\ i # Special
    /\ state[i] = "right_acquired"
    /\ forks[Left(i)] = 0
    /\ forks' = [forks EXCEPT ![Left(i)] = 1]
    /\ state' = [state EXCEPT ![i] = "left_acquired"]

AcquireSecondSpecial(i) ==
    /\ i = Special
    /\ state[i] = "left_acquired"
    /\ forks[Right(i)] = 0
    /\ forks' = [forks EXCEPT ![Right(i)] = 1]
    /\ state' = [state EXCEPT ![i] = "right_acquired"]

EatNonSpecial(i) ==
    /\ i # Special
    /\ state[i] = "left_acquired"
    /\ state' = [state EXCEPT ![i] = "eating"]
    /\ UNCHANGED forks

EatSpecial(i) ==
    /\ i = Special
    /\ state[i] = "right_acquired"
    /\ state' = [state EXCEPT ![i] = "eating"]
    /\ UNCHANGED forks

Release(i) ==
    /\ state[i] = "eating"
    /\ forks' = [forks EXCEPT ![Left(i)] = 0, ![Right(i)] = 0]
    /\ state' = [state EXCEPT ![i] = "thinking"]

PhiloAction(i) ==
    AcquireFirstNonSpecial(i) \/ AcquireFirstSpecial(i) \/
    AcquireSecondNonSpecial(i) \/ AcquireSecondSpecial(i) \/
    EatNonSpecial(i) \/ EatSpecial(i) \/ Release(i)

Next == \E i ∈ 1..N : PhiloAction(i)

Fairness == \A i ∈ 1..N : SF_vars(PhiloAction(i))

Spec == Init /\ [][Next]_vars /\ Fairness

SafetyInvariant == [] NoAdjacentEating
LivenessProperty == \A i ∈ 1..N : []<>(state[i] = "eating")