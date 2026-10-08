MODULE DiningPhilosophers
EXTENDS Naturals, Sequences

CONSTANT N \in Nat
ASSUME N > 0

VARIABLES state, forks

Left(i) == i
Right(i) == IF i < N THEN i + 1 ELSE 1

Init ==
    /\ state = [i \in 1..N |-> "thinking"]
    /\ forks = [f \in 1..N |-> 0]

Eat(p) ==
    /\ p \in 1..N
    /\ state[p] = "thinking"
    /\ forks[Left(p)] = 0
    /\ forks[Right(p)] = 0
    /\ forks' = [forks EXCEPT ![Left(p)] = p, ![Right(p)] = p]
    /\ state' = [state EXCEPT ![p] = "eating"]

FinishEating(p) ==
    /\ p \in 1..N
    /\ state[p] = "eating"
    /\ forks[Left(p)] = p
    /\ forks[Right(p)] = p
    /\ forks' = [forks EXCEPT ![Left(p)] = 0, ![Right(p)] = 0]
    /\ state' = [state EXCEPT ![p] = "thinking"]

Next == \E p \in 1..N : (Eat(p) \/ FinishEating(p))

NoAdjacentEating ==
    \A i,j \in 1..N :
        ((i # j) /\ (Right(i)=j \/ Left(i)=j)) => ~(state[i]="eating" /\ state[j]="eating")

ForkIntegrity ==
    \A f \in 1..N :
        forks[f] = 0 \/ (forks[f] \in 1..N /\ state[forks[f]] = "eating")

StarvationFreedom == \A p \in 1..N : []<>(state[p] = "eating")

NoDeadlock == [] <> (\E p \in 1..N : Enabled(Eat(p)))

Spec ==
    Init
    /\ [][Next]_vars
    /\ \A p \in 1..N : WF_action(Eat(p))
    /\ \A p \in 1..N : WF_action(FinishEating(p))

THEOREM SafetyInvariants == Spec => NoAdjacentEating /\ ForkIntegrity

THEOREM LivenessStarvationFreedom == Spec => StarvationFreedom

THEOREM AbsenceOfDeadlock == Spec => NoDeadlock
