------------------------------ MODULE DiningPhilosophers ------------------------------
(***************************************************************************)
(* Dining Philosophers for N philosophers arranged in a ring.              *)
(*                                                                         *)
(* sem[f] = 1 means fork f is available; sem[f] = 0 means it is held.      *)
(* Philosopher p's right fork is fork p, and its left fork is fork         *)
(* (p+1) % N.                                                              *)
(*                                                                         *)
(* To avoid deadlock, the design breaks symmetry. Philosophers 1..N-1      *)
(* pick up the right fork and then the left fork. Philosopher 0 picks up   *)
(* the left fork and then the right fork.                                  *)
(*                                                                         *)
(* --algorithm DiningPhilosophers {                                        *)
(*   variables sem = [f \in 0..N-1 |-> 1];                                 *)
(*   process (Philosopher \in 0..N-1) {                                    *)
(*     Lp: while (TRUE) {                                                  *)
(*           await sem[First(self)] = 1;                                   *)
(*           sem[First(self)] := 0;                                        *)
(*     L2:   await sem[Second(self)] = 1;                                  *)
(*           sem[Second(self)] := 0;                                       *)
(*     Eat:  sem[First(self)] := 1 || ... ; \* release both forks          *)
(*         }                                                               *)
(*   }                                                                     *)
(* }                                                                       *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 2

Philosophers == 0..N-1
Forks        == 0..N-1

RightFork(p) == p
LeftFork(p)  == (p + 1) % N

\* Order of fork acquisition: philosopher 0 is reversed.
First(p)  == IF p = 0 THEN LeftFork(p)  ELSE RightFork(p)
Second(p) == IF p = 0 THEN RightFork(p) ELSE LeftFork(p)

\* BEGIN TRANSLATION
VARIABLES sem, pc

vars == << sem, pc >>

ProcSet == Philosophers

Init == /\ sem = [f \in Forks |-> 1]
        /\ pc  = [self \in ProcSet |-> "Lp"]

\* Acquire the first fork.
Lp(self) == /\ pc[self] = "Lp"
            /\ sem[First(self)] = 1
            /\ sem' = [sem EXCEPT ![First(self)] = 0]
            /\ pc'  = [pc EXCEPT ![self] = "L2"]

\* Acquire the second fork.
L2(self) == /\ pc[self] = "L2"
            /\ sem[Second(self)] = 1
            /\ sem' = [sem EXCEPT ![Second(self)] = 0]
            /\ pc'  = [pc EXCEPT ![self] = "Eat"]

\* Eat, then release both forks.
Eat(self) == /\ pc[self] = "Eat"
             /\ sem' = [sem EXCEPT ![First(self)] = 1, ![Second(self)] = 1]
             /\ pc'  = [pc EXCEPT ![self] = "Lp"]

Philosopher(self) == Lp(self) \/ L2(self) \/ Eat(self)

Next == \E self \in Philosophers : Philosopher(self)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Philosophers : SF_vars(Philosopher(self))
\* END TRANSLATION

-----------------------------------------------------------------------------
(* Properties *)

TypeOK == /\ sem \in [Forks -> {0, 1}]
          /\ pc  \in [ProcSet -> {"Lp", "L2", "Eat"}]

\* Adjacent philosophers never eat at the same time.
Invariant == \A p \in Philosophers :
                (pc[p] = "Eat") => (pc[(p + 1) % N] # "Eat")

\* Starvation freedom: every philosopher eats infinitely often.
StarvationFree == \A p \in Philosophers : []<>(pc[p] = "Eat")

THEOREM Spec => [](TypeOK /\ Invariant)
THEOREM Spec => StarvationFree
=============================================================================