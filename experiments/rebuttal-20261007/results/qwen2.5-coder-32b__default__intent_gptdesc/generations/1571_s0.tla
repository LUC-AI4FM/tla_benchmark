------------------------------- MODULE DiningPhilosophers -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N
ASSUME N \in Nat /\ N > 0

VARIABLES forks, states

PHILOSOPHERS == {p \in 1..N}
FORKS == {f \in 1..N}

LEFT_FORK(p) == (p - 1) % N + 1
RIGHT_FORK(p) == p

Init == 
    /\ forks = [f \in FORKS |-> FALSE]
    /\ states = [p \in PHILOSOPHERS |-> "thinking"]

Next ==
    \/ \E p \in PHILOSOPHERS : states[p] = "thinking" /\ forks[LEFT_FORK(p)] = FALSE /\ forks[RIGHT_FORK(p)] = FALSE
        /\ forks' = [forks EXCEPT ![LEFT_FORK(p)] = TRUE, ![RIGHT_FORK(p)] = TRUE]
        /\ states' = [states EXCEPT ![p] = "eating"]
    \/ \E p \in PHILOSOPHERS : states[p] = "eating"
        /\ forks' = [forks EXCEPT ![LEFT_FORK(p)] = FALSE, ![RIGHT_FORK(p)] = FALSE]
        /\ states' = [states EXCEPT ![p] = "thinking"]

Spec ==
    /\ Init
    /\ [][Next]_<<forks, states>>
    /\ WF_next(<<forks, states>>)

MutualExclusion == 
    \A p1, p2 \in PHILOSOPHERS : p1 # p2 => ~ (states[p1] = "eating" /\ states[p2] = "eating" /\ LEFT_FORK(p1) = RIGHT_FORK(p2))

NoDeadlock ==
    \A S \subseteq PHILOSOPHERS :
        (\E p \in S : states[p] = "thinking" /\ forks[LEFT_FORK(p)] = FALSE /\ forks[RIGHT_FORK(p)] = FALSE)
        \/ ~(\A p \in S : states[p] = "eating")

StarvationFreedom ==
    \A p \in PHILOSOPHERS :
        [](<>[]states[p] = "eating"))

ResourceIntegrity ==
    \A f \in FORKS : 
        (Cardinality({p \in PHILOSOPHERS : forks[f]}) <= 1)

Properties ==
    /\ MutualExclusion
    /\ NoDeadlock
    /\ StarvationFreedom
    /\ ResourceIntegrity

=============================================================================