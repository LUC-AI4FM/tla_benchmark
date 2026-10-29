---- MODULE DiningPhilosophers ----
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

VARIABLES state, fork

vars == <<state, fork>>

Phil  == 0..(N - 1)
ForkIds == 0..(N - 1)

\* A value that is not a philosopher id, used to mark a free fork
Free == N

States == {"thinking", "hungry", "eating"}

LeftFork(p)  == p
RightFork(p) == (p + 1) % N
Forks(p)     == {LeftFork(p), RightFork(p)}

LeftNbr(p)  == (p + N - 1) % N
RightNbr(p) == (p + 1) % N

Adjacent(p, q) == /\ p # q
                  /\ \/ q = LeftNbr(p)
                     \/ q = RightNbr(p)

-----------------------------------------------------------------------------

TypeOK ==
    /\ state \in [Phil -> States]
    /\ fork \in [ForkIds -> Phil \cup {Free}]

Init ==
    /\ state = [p \in Phil |-> "thinking"]
    /\ fork = [f \in ForkIds |-> Free]

\* A thinking philosopher becomes hungry (starts trying to eat)
GetHungry(p) ==
    /\ state[p] = "thinking"
    /\ state' = [state EXCEPT ![p] = "hungry"]
    /\ UNCHANGED fork

\* A hungry philosopher acquires both adjacent forks (only if both free)
\* and starts eating. No particular acquisition order is imposed.
Eat(p) ==
    /\ state[p] = "hungry"
    /\ \A f \in Forks(p) : fork[f] = Free
    /\ fork' = [f \in ForkIds |-> IF f \in Forks(p) THEN p ELSE fork[f]]
    /\ state' = [state EXCEPT ![p] = "eating"]

\* An eating philosopher releases both forks and returns to thinking
Release(p) ==
    /\ state[p] = "eating"
    /\ fork' = [f \in ForkIds |-> IF f \in Forks(p) THEN Free ELSE fork[f]]
    /\ state' = [state EXCEPT ![p] = "thinking"]

Next == \E p \in Phil : GetHungry(p) \/ Eat(p) \/ Release(p)

Fairness ==
    \A p \in Phil :
        /\ WF_vars(GetHungry(p))
        /\ SF_vars(Eat(p))
        /\ WF_vars(Release(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety properties

\* No two adjacent philosophers eat at the same time
MutualExclusion ==
    \A p, q \in Phil :
        (Adjacent(p, q) /\ state[p] = "eating") => state[q] # "eating"

\* An eating philosopher holds both of its forks
EatingHoldsForks ==
    \A p \in Phil :
        state[p] = "eating" => \A f \in Forks(p) : fork[f] = p

\* Each fork is held by at most one philosopher, only by an adjacent one,
\* and only while that philosopher is eating (otherwise it is free)
ForkIntegrity ==
    \A f \in ForkIds :
        fork[f] # Free =>
            /\ f \in Forks(fork[f])
            /\ state[fork[f]] = "eating"

Invariant ==
    /\ TypeOK
    /\ MutualExclusion
    /\ EatingHoldsForks
    /\ ForkIntegrity

-----------------------------------------------------------------------------
\* Liveness / progress properties

\* Absence of deadlock: some action is always enabled
DeadlockFreedom == [](ENABLED Next)

\* Starvation freedom: every philosopher eats infinitely often
StarvationFreedom == \A p \in Phil : []<>(state[p] = "eating")

\* Hungry philosophers eventually eat
HungryLeadsToEating == \A p \in Phil : (state[p] = "hungry") ~> (state[p] = "eating")

\* Forks are returned after eating
ForksReturned ==
    \A p \in Phil :
        (state[p] = "eating") ~> (state[p] = "thinking" /\ \A f \in Forks(p) : fork[f] # p)

=============================================================================