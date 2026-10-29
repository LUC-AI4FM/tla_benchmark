------------------------- MODULE DiningPhilosophers -------------------------
(***************************************************************************)
(* Dining Philosophers, Chandy-Misra style solution.                       *)
(*                                                                         *)
(* Philosophers 1..NP sit in a circle.  Fork f is shared by philosopher f  *)
(* and philosopher f+1 (wrapping around, so fork NP is shared by           *)
(* philosopher NP and philosopher 1).  Every fork has a holder and a       *)
(* cleanliness flag.  Initially every fork is dirty and held by the        *)
(* lower-numbered of its two adjacent philosophers.                        *)
(*                                                                         *)
(* A philosopher holding a dirty fork hands it, cleaned, to the neighbor   *)
(* that shares it.  A philosopher keeps clean forks until it eats.  A      *)
(* hungry philosopher eats only when it holds both its forks and both are  *)
(* clean.  After eating, both forks become dirty.                          *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT NP

ASSUME NP \in Nat /\ NP >= 1

VARIABLES forks, state

vars == <<forks, state>>

Philosophers == 1..NP
Forks        == 1..NP

States == {"thinking", "hungry", "eating"}

ForkType == [holder : Philosophers, clean : BOOLEAN]

\* Neighbors in the circle
RightPhilosopher(p) == IF p = NP THEN 1 ELSE p + 1
LeftPhilosopher(p)  == IF p = 1 THEN NP ELSE p - 1

\* Fork f is shared by philosopher f and RightPhilosopher(f)
RightFork(p) == p
LeftFork(p)  == LeftPhilosopher(p)

MyForks(p) == {LeftFork(p), RightFork(p)}

\* The other philosopher sharing fork f with philosopher p
OtherSharer(f, p) == IF p = f THEN RightPhilosopher(f) ELSE f

\* Lower-numbered of the two philosophers adjacent to fork f
LowerSharer(f) == IF f < RightPhilosopher(f) THEN f ELSE RightPhilosopher(f)

IsHoldingBothForks(p) ==
    /\ forks[LeftFork(p)].holder = p
    /\ forks[RightFork(p)].holder = p

BothForksAreClean(p) ==
    /\ forks[LeftFork(p)].clean
    /\ forks[RightFork(p)].clean

CanEat(p) == IsHoldingBothForks(p) /\ BothForksAreClean(p)

-----------------------------------------------------------------------------

Init ==
    /\ forks = [f \in Forks |-> [holder |-> LowerSharer(f), clean |-> FALSE]]
    /\ state = [p \in Philosophers |-> "thinking"]

\* Hand a dirty fork, after cleaning it, to the neighbor sharing it
PassFork(p) ==
    \E f \in MyForks(p) :
        /\ forks[f].holder = p
        /\ ~forks[f].clean
        /\ forks' = [forks EXCEPT ![f] = [holder |-> OtherSharer(f, p),
                                          clean  |-> TRUE]]
        /\ UNCHANGED state

BecomeHungry(p) ==
    /\ state[p] = "thinking"
    /\ state' = [state EXCEPT ![p] = "hungry"]
    /\ UNCHANGED forks

Eat(p) ==
    /\ state[p] = "hungry"
    /\ CanEat(p)
    /\ state' = [state EXCEPT ![p] = "eating"]
    /\ UNCHANGED forks

FinishEating(p) ==
    /\ state[p] = "eating"
    /\ state' = [state EXCEPT ![p] = "thinking"]
    /\ forks' = [f \in Forks |->
                   IF f \in MyForks(p)
                     THEN [holder |-> p, clean |-> FALSE]
                     ELSE forks[f]]

Philosopher(p) ==
    \/ PassFork(p)
    \/ BecomeHungry(p)
    \/ Eat(p)
    \/ FinishEating(p)

Next == \E p \in Philosophers : Philosopher(p)

Fairness == \A p \in Philosophers : WF_vars(Philosopher(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------

TypeOK ==
    /\ forks \in [Forks -> ForkType]
    /\ state \in [Philosophers -> States]

ExclusiveAccess ==
    \A p, q \in Philosophers :
        (p # q /\ MyForks(p) \cap MyForks(q) # {})
            => ~(state[p] = "eating" /\ state[q] = "eating")

NobodyStarves ==
    \A p \in Philosophers : []<>(state[p] = "eating")

=============================================================================