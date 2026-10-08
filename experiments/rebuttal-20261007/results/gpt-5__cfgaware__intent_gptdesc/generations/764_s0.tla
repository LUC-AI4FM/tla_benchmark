------------------------------ MODULE DiningPhilosophers ------------------------------

EXTENDS Naturals

CONSTANTS
    N,               \* Number of philosophers (N >= 2)
    ForkState,       \* Abstract set of fork states
    Permitting       \* Subset of ForkState that permits eating

ASSUME
    /\ N \in Nat /\ N >= 2
    /\ Permitting \subseteq ForkState
    /\ Permitting # {}

P == 0 .. (N - 1)

Next(p) == IF p < N - 1 THEN p + 1 ELSE 0
Pred(p) == IF p > 0 THEN p - 1 ELSE N - 1

RightFork(p) == {p, Next(p)}
LeftFork(p) == {Pred(p), p}
AdjacentForks(p) == {LeftFork(p), RightFork(p)}

Forks == { RightFork(p) : p \in P }

Modes == {"Thinking", "Hungry", "Eating"}

VARIABLES
    mode,     \* [P -> Modes]
    owner,    \* [Forks -> P], with owner[f] \in f
    fstate    \* [Forks -> ForkState]

vars == << mode, owner, fstate >>

TypeOK ==
    /\ mode \in [P -> Modes]
    /\ owner \in [Forks -> P]
    /\ \A f \in Forks: owner[f] \in f
    /\ fstate \in [Forks -> ForkState]

Owned(p) == { f \in Forks : owner[f] = p }

EatingAllowed(p) ==
    /\ AdjacentForks(p) \subseteq Owned(p)
    /\ \A f \in AdjacentForks(p): fstate[f] \in Permitting

Init ==
    /\ mode = [p \in P |-> "Thinking"]
    /\ owner \in [Forks -> P]
    /\ \A f \in Forks: owner[f] \in f
    /\ fstate \in [Forks -> ForkState]

ThinkToHungry(p) ==
    /\ p \in P
    /\ mode[p] = "Thinking"
    /\ mode' = [mode EXCEPT ![p] = "Hungry"]
    /\ owner' = owner
    /\ fstate' = fstate

HungryToEat(p) ==
    /\ p \in P
    /\ mode[p] = "Hungry"
    /\ EatingAllowed(p)
    /\ mode' = [mode EXCEPT ![p] = "Eating"]
    /\ owner' = owner
    /\ \E st' \in [Forks -> ForkState]:
         /\ \A f \in Forks:
               IF f \in AdjacentForks(p) THEN TRUE ELSE st'[f] = fstate[f]
         /\ fstate' = st'

EatToThink(p) ==
    /\ p \in P
    /\ mode[p] = "Eating"
    /\ mode' = [mode EXCEPT ![p] = "Thinking"]
    /\ owner' = owner
    /\ \E st' \in [Forks -> ForkState]:
         /\ \A f \in Forks:
               IF f \in AdjacentForks(p) THEN TRUE ELSE st'[f] = fstate[f]
         /\ fstate' = st'

PassFork(p, q) ==
    /\ p \in P /\ q \in {Next(p), Pred(p)}
    /\ LET f == {p, q} IN
         /\ owner[f] = p
         /\ mode[p] # "Eating"     \* cannot give up an in-use adjacent fork
         /\ mode' = mode
         /\ owner' = [owner EXCEPT ![f] = q]
         /\ \E st' \in [Forks -> ForkState]:
              /\ \A x \in Forks:
                    IF x = {p, q} THEN TRUE ELSE st'[x] = fstate[x]
              /\ fstate' = st'

Proc(p) ==
    ThinkToHungry(p)
    \/ HungryToEat(p)
    \/ EatToThink(p)
    \/ \E q \in {Next(p), Pred(p)}: PassFork(p, q)

Next ==
    \E p \in P: Proc(p)

Fairness ==
    \A p \in P: WF_vars(Proc(p))

Spec ==
    Init /\ [][Next]_vars /\ Fairness

\* Safety: no two neighbors eat simultaneously
MutualExclusion ==
    \A p \in P:
        mode[p] = "Eating"
        => /\ mode[Next(p)] # "Eating"
           /\ mode[Pred(p)] # "Eating"

Safety == MutualExclusion

\* Invariants (state): typing and ownership, plus eating implies owning both adjacent forks
OwnershipInv == \A f \in Forks: owner[f] \in f
EatingOwnsAdjacent == \A p \in P: mode[p] = "Eating" => AdjacentForks(p) \subseteq Owned(p)

\* Liveness: under fairness, hungry eventually eats (no starvation)
NoStarvation ==
    \A p \in P: [](mode[p] = "Hungry" => <>(mode[p] = "Eating"))

\* Progress: no global deadlock (there is always some enabled next step)
DeadlockFreedom ==
    []<>(ENABLED Next)

==============================