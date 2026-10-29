------------------------------ MODULE DiningPhilosophers ------------------------------
EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat

VARIABLES forks, pc

vars == << forks, pc >>

Procs == 0 .. (N - 1)

\* Fork indices: philosopher p sits between fork p (left) and fork (p+1) % N (right)
LeftFork(p)  == p
RightFork(p) == (p + 1) % N

\* All philosophers except philosopher 0 take the right fork first;
\* philosopher 0 takes the left fork first.
FirstFork(p)  == IF p = 0 THEN LeftFork(p)  ELSE RightFork(p)
SecondFork(p) == IF p = 0 THEN RightFork(p) ELSE LeftFork(p)

\* Binary semaphore operations: 1 = available, 0 = taken
P(f) == /\ forks[f] = 1
        /\ forks' = [forks EXCEPT ![f] = 0]

TypeOK == /\ forks \in [Procs -> {0, 1}]
          /\ pc \in [Procs -> {"first", "second", "eat", "release"}]

Init == /\ forks = [f \in Procs |-> 1]
        /\ pc = [p \in Procs |-> "first"]

TakeFirst(self) ==
    /\ pc[self] = "first"
    /\ P(FirstFork(self))
    /\ pc' = [pc EXCEPT ![self] = "second"]

TakeSecond(self) ==
    /\ pc[self] = "second"
    /\ P(SecondFork(self))
    /\ pc' = [pc EXCEPT ![self] = "eat"]

Eat(self) ==
    /\ pc[self] = "eat"
    /\ pc' = [pc EXCEPT ![self] = "release"]
    /\ UNCHANGED forks

Release(self) ==
    /\ pc[self] = "release"
    /\ forks' = [forks EXCEPT ![LeftFork(self)] = 1, ![RightFork(self)] = 1]
    /\ pc' = [pc EXCEPT ![self] = "first"]

phil(self) == TakeFirst(self) \/ TakeSecond(self) \/ Eat(self) \/ Release(self)

Next == \E self \in Procs : phil(self)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Procs : SF_vars(phil(self))

\* Safety: no two adjacent philosophers eat at the same time
Invariant ==
    \A p \in Procs :
        (pc[p] = "eat" /\ RightFork(p) # p) => pc[RightFork(p)] # "eat"

\* Liveness: every philosopher eats infinitely often
StarvationFree == \A p \in Procs : []<>(pc[p] = "eat")

=============================================================================