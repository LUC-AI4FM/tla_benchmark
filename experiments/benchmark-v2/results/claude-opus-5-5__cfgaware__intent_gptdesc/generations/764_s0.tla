------------------------- MODULE DiningPhilosophers -------------------------
(***************************************************************************)
(* Dining philosophers with a fork-passing protocol in the style of        *)
(* Chandy and Misra (clean and dirty forks).                               *)
(*                                                                         *)
(* Philosophers are numbered 1..NP and sit around a round table.  Fork f   *)
(* lies between philosopher f and philosopher (f % NP) + 1.  Philosopher p *)
(* uses fork p (its right fork) and fork LeftFork(p) (the fork it shares   *)
(* with its left neighbour).                                               *)
(*                                                                         *)
(* Each fork is held by exactly one of its two adjacent philosophers and   *)
(* is either clean or dirty.                                               *)
(*   - Initially every fork is dirty and is held by the lower-numbered of  *)
(*     its two philosophers, which makes the precedence graph acyclic.     *)
(*   - A hungry philosopher implicitly requests the forks it lacks.        *)
(*   - A philosopher that holds a dirty fork, and is not eating, hands it  *)
(*     to a hungry neighbour.  The fork is cleaned when it is passed.      *)
(*   - A hungry philosopher eats when it holds both forks and each fork is *)
(*     usable.  A fork is usable if it is clean, or if no neighbour is     *)
(*     hungry for it.  Eating makes both forks dirty.                      *)
(*   - An eating philosopher eventually returns to thinking.               *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT NP

ASSUME NP \in Nat \ {0}

VARIABLES forks, state

vars == <<forks, state>>

Phils == 1..NP
Forks == 1..NP

States == {"thinking", "hungry", "eating"}

(* The forks used by philosopher p *)
RightFork(p) == p
LeftFork(p)  == IF p = 1 THEN NP ELSE p - 1
ForksOf(p)   == {LeftFork(p), RightFork(p)}

(* The two philosophers adjacent to fork f *)
Adjacent(f) == {f, (f % NP) + 1}

(* The philosopher, other than p, that shares fork f *)
Other(f, p) == IF p = f THEN (f % NP) + 1 ELSE f

(* The two neighbours of philosopher p *)
LeftNeighbor(p)  == IF p = 1 THEN NP ELSE p - 1
RightNeighbor(p) == (p % NP) + 1

-----------------------------------------------------------------------------

TypeOK ==
  /\ forks \in [Forks -> [holder : Phils, clean : BOOLEAN]]
  /\ state \in [Phils -> States]

(* Every fork is held by exactly one of its two adjacent philosophers *)
ForkHeldByNeighbor ==
  \A f \in Forks : forks[f].holder \in Adjacent(f)

Init ==
  /\ forks = [f \in Forks |->
                [holder |-> IF f = NP THEN 1 ELSE f, clean |-> FALSE]]
  /\ state = [p \in Phils |-> "thinking"]

(* A thinking philosopher becomes hungry *)
BecomeHungry(p) ==
  /\ state[p] = "thinking"
  /\ state' = [state EXCEPT ![p] = "hungry"]
  /\ UNCHANGED forks

(* Philosopher p hands dirty fork f to a hungry neighbour that requests  *)
(* it.  The fork is cleaned when it is passed.                           *)
GiveFork(p, f) ==
  LET q == Other(f, p) IN
  /\ f \in ForksOf(p)
  /\ forks[f].holder = p
  /\ ~ forks[f].clean
  /\ q # p
  /\ state[q] = "hungry"
  /\ state[p] # "eating"
  /\ forks' = [forks EXCEPT ![f] = [holder |-> q, clean |-> TRUE]]
  /\ UNCHANGED state

(* Fork f is in a state that lets philosopher p eat with it *)
CanUse(p, f) ==
  /\ forks[f].holder = p
  /\ \/ forks[f].clean
     \/ Other(f, p) = p
     \/ state[Other(f, p)] # "hungry"

(* A hungry philosopher that holds two usable forks eats. *)
(* Eating makes both forks dirty.                         *)
Eat(p) ==
  /\ state[p] = "hungry"
  /\ \A f \in ForksOf(p) : CanUse(p, f)
  /\ state' = [state EXCEPT ![p] = "eating"]
  /\ forks' = [f \in Forks |->
                 IF f \in ForksOf(p)
                   THEN [holder |-> p, clean |-> FALSE]
                   ELSE forks[f]]

(* An eating philosopher finishes and goes back to thinking *)
Think(p) ==
  /\ state[p] = "eating"
  /\ state' = [state EXCEPT ![p] = "thinking"]
  /\ UNCHANGED forks

Next ==
  \E p \in Phils :
     \/ BecomeHungry(p)
     \/ \E f \in Forks : GiveFork(p, f)
     \/ Eat(p)
     \/ Think(p)

(* Thinking may last forever, so BecomeHungry has no fairness condition. *)
(* Every other action of a philosopher process is weakly fair.           *)
Fairness ==
  \A p \in Phils :
     /\ \A f \in Forks : WF_vars(GiveFork(p, f))
     /\ WF_vars(Eat(p))
     /\ WF_vars(Think(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Correctness properties *)

(* Safety: two neighbouring philosophers never eat at the same time *)
ExclusiveAccess ==
  \A p \in Phils :
     state[p] = "eating" =>
        /\ (LeftNeighbor(p) # p  => state[LeftNeighbor(p)] # "eating")
        /\ (RightNeighbor(p) # p => state[RightNeighbor(p)] # "eating")

(* Combined invariant *)
Inv == TypeOK /\ ForkHeldByNeighbor /\ ExclusiveAccess

(* Liveness: every hungry philosopher eventually eats *)
NobodyStarves ==
  \A p \in Phils : (state[p] = "hungry") ~> (state[p] = "eating")

(* Progress: some step is always enabled, so there is no global deadlock *)
NoDeadlock == [](ENABLED Next)

THEOREM Spec => []Inv
THEOREM Spec => NobodyStarves
=============================================================================