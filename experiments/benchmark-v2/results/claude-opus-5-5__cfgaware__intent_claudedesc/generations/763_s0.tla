------------------------- MODULE DiningPhilosophers -------------------------
(***************************************************************************)
(* Dining Philosophers with the Chandy-Misra (hygienic) solution.          *)
(*                                                                         *)
(* Philosophers 0..NP-1 sit in a circle. Fork f lies between philosopher f *)
(* and philosopher (f+1) % NP. Philosopher p uses forks p and (p-1) % NP.  *)
(*                                                                         *)
(* Each fork records its holder and whether it is clean or dirty.          *)
(*  - Initially every fork is dirty and is held by the lower-numbered of   *)
(*    its two neighbours. This makes the precedence graph acyclic.         *)
(*  - A holder must hand a dirty fork to a hungry neighbour who requests   *)
(*    it, unless the holder is eating. The fork is cleaned when it is      *)
(*    handed over.                                                         *)
(*  - A holder keeps a clean fork.                                         *)
(*  - A hungry philosopher who holds both forks eats. Eating makes both    *)
(*    forks dirty.                                                         *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT NP

ASSUME NP \in Nat /\ NP >= 2

Philosophers == 0 .. NP-1
Forks        == 0 .. NP-1

LeftPhil(p)  == (p + NP - 1) % NP
RightPhil(p) == (p + 1) % NP

\* The two philosophers that share fork f
Users(f) == {f, RightPhil(f)}

\* The forks used by philosopher p
ForksOf(p) == {p, LeftPhil(p)}

\* The other philosopher sharing fork f with p
OtherEnd(f, p) == IF p = f THEN RightPhil(f) ELSE f

Min(a, b) == IF a < b THEN a ELSE b

VARIABLES forks, state

vars == <<forks, state>>

States == {"thinking", "hungry", "eating"}

TypeOK ==
    /\ forks \in [Forks -> [holder : Philosophers, clean : BOOLEAN]]
    /\ \A f \in Forks : forks[f].holder \in Users(f)
    /\ state \in [Philosophers -> States]

Init ==
    /\ forks = [f \in Forks |-> [holder |-> Min(f, RightPhil(f)),
                                 clean  |-> FALSE]]
    /\ state = [p \in Philosophers |-> "thinking"]

HoldsBoth(p) == \A f \in ForksOf(p) : forks[f].holder = p

-----------------------------------------------------------------------------
(* Actions *)

\* A thinking philosopher becomes hungry.
BecomeHungry(p) ==
    /\ state[p] = "thinking"
    /\ state' = [state EXCEPT ![p] = "hungry"]
    /\ UNCHANGED forks

\* Philosopher p hands its dirty fork f to the hungry neighbour that
\* requested it. p must not be eating. The fork is cleaned on transfer.
GiveFork(p, f) ==
    LET q == OtherEnd(f, p) IN
    /\ f \in ForksOf(p)
    /\ forks[f].holder = p
    /\ ~forks[f].clean
    /\ state[p] # "eating"
    /\ state[q] = "hungry"
    /\ q # p
    /\ forks' = [forks EXCEPT ![f] = [holder |-> q, clean |-> TRUE]]
    /\ UNCHANGED state

\* A hungry philosopher holding both forks starts eating.
\* Both forks become dirty.
Eat(p) ==
    /\ state[p] = "hungry"
    /\ HoldsBoth(p)
    /\ state' = [state EXCEPT ![p] = "eating"]
    /\ forks' = [f \in Forks |->
                    IF f \in ForksOf(p)
                    THEN [holder |-> p, clean |-> FALSE]
                    ELSE forks[f]]

\* An eating philosopher finishes and goes back to thinking.
\* The forks stay dirty, so they are released to any requesting neighbour.
FinishEating(p) ==
    /\ state[p] = "eating"
    /\ state' = [state EXCEPT ![p] = "thinking"]
    /\ forks' = [f \in Forks |->
                    IF f \in ForksOf(p)
                    THEN [forks[f] EXCEPT !.clean = FALSE]
                    ELSE forks[f]]

Next ==
    \E p \in Philosophers :
        \/ BecomeHungry(p)
        \/ \E f \in ForksOf(p) : GiveFork(p, f)
        \/ Eat(p)
        \/ FinishEating(p)

Fairness ==
    \A p \in Philosophers :
        /\ WF_vars(Eat(p))
        /\ WF_vars(FinishEating(p))
        /\ \A f \in ForksOf(p) : WF_vars(GiveFork(p, f))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Properties *)

\* No two adjacent philosophers eat at the same time.
ExclusiveAccess ==
    \A p \in Philosophers :
        state[p] = "eating" =>
            /\ state[RightPhil(p)] # "eating"
            /\ state[LeftPhil(p)] # "eating"
            /\ HoldsBoth(p)

\* Deadlock freedom: if anyone is hungry, some step of the protocol is enabled.
NoDeadlock ==
    (\E p \in Philosophers : state[p] = "hungry") =>
        \E p \in Philosophers :
            \/ ENABLED Eat(p)
            \/ ENABLED FinishEating(p)
            \/ \E f \in ForksOf(p) : ENABLED GiveFork(p, f)

\* Starvation freedom: every hungry philosopher eventually eats.
StarvationFreedom ==
    \A p \in Philosophers : (state[p] = "hungry") ~> (state[p] = "eating")

=============================================================================