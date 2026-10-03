---- MODULE DiningPhilosophers ----
EXTENDS Integers, TLC

CONSTANT N
ASSUME N \in Nat /\ N > 1

Philosophers == 0..(N-1)
Forks == 0..(N-1)

VARIABLES pc, forks

vars == <<pc, forks>>

\* -- Helper definitions for the ring topology. Philosopher p sits between
\* -- their Left fork (p) and their Right fork ((p+1)%N).
Left(p) == p
Right(p) == (p + 1) % N

\* -- Asymmetric fork acquisition to prevent deadlock: philosopher 0 picks up
\* -- left-then-right, while others (1..N-1) pick up right-then-left.
FirstFork(p) == IF p = 0 THEN Left(p) ELSE Right(p)
SecondFork(p) == IF p = 0 THEN Right(p) ELSE Left(p)

\* -- The state of a philosopher can be "thinking", "hungry" (waiting for the
\* -- first fork), "got_first" (waiting for the second), or "eating".
\* -- The forks array is semaphore-like: TRUE means available, FALSE means taken.
TypeOK ==
    /\ pc \in [Philosophers -> {"thinking", "hungry", "got_first", "eating"}]
    /\ forks \in [Forks -> BOOLEAN]

\* -- Initial state: all philosophers are thinking and all forks are available.
Init ==
    /\ pc = [p \in Philosophers |-> "thinking"]
    /\ forks = [f \in Forks |-> TRUE]

\* -- State transitions (actions) for a single philosopher p

\* A thinking philosopher can decide to become hungry.
BecomeHungry(p) ==
    /\ pc[p] = "thinking"
    /\ pc' = [pc EXCEPT ![p] = "hungry"]
    /\ UNCHANGED forks

\* A hungry philosopher picks up their first fork if it is available.
GetFirstFork(p) ==
    /\ pc[p] = "hungry"
    /\ forks[FirstFork(p)]
    /\ pc' = [pc EXCEPT ![p] = "got_first"]
    /\ forks' = [forks EXCEPT ![FirstFork(p)] = FALSE]

\* A philosopher with one fork picks up their second fork if it is available.
GetSecondFork(p) ==
    /\ pc[p] = "got_first"
    /\ forks[SecondFork(p)]
    /\ pc' = [pc EXCEPT ![p] = "eating"]
    /\ forks' = [forks EXCEPT ![SecondFork(p)] = FALSE]

\* An eating philosopher puts down both forks and starts thinking again.
PutDownForks(p) ==
    /\ pc[p] = "eating"
    /\ pc' = [pc EXCEPT ![p] = "thinking"]
    /\ forks' = [forks EXCEPT ![FirstFork(p)] = TRUE, ![SecondFork(p)] = TRUE]

\* The action of philosopher p is the disjunction of their possible atomic steps.
P(p) ==
    \/ BecomeHungry(p)
    \/ GetFirstFork(p)
    \/ GetSecondFork(p)
    \/ PutDownForks(p)

\* The next-state relation is that some philosopher takes an enabled step.
Next == \E p \in Philosophers : P(p)

\* The full specification, including strong fairness for each philosopher process.
\* Strong fairness ensures that if a philosopher's set of actions is infinitely
\* often enabled, one of those actions will eventually be taken. This is
\* crucial for proving liveness (starvation-freedom).
Spec == Init /\ [][Next]_vars /\ \A p \in Philosophers : SF_vars(P(p))

\* -- Properties

\* Safety Invariant: No two adjacent philosophers can be eating at the same time.
MutualExclusion ==
    \A p \in Philosophers : pc[p] = "eating" => pc[(p + 1) % N] # "eating"

\* Liveness Property: Every philosopher that becomes hungry eventually gets to eat.
StarvationFreedom ==
    \A p \in Philosophers : pc[p] = "hungry" ~> pc[p] = "eating"

=============================================================================