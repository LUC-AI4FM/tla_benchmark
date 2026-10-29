---------------------------- MODULE DiningPhilosophers ----------------------------
EXTENDS Naturals, TLC

CONSTANT N

ASSUME N \in Nat /\ N > 1

(* Fork i lies between philosopher i and philosopher (i+1) % N.          *)
(* For philosopher i, the right fork is fork i and the left fork is       *)
(* fork (i+1) % N.  sem[f] = 1 means fork f is available, 0 means taken.  *)

Right(i) == i
Left(i)  == (i + 1) % N

VARIABLES sem, pc

vars == << sem, pc >>

ProcSet == (1..N-1) \cup {0}

Init == /\ sem = [f \in 0..N-1 |-> 1]
        /\ pc = [self \in ProcSet |-> "l0"]

(***************************************************************************)
(* Philosophers 1..N-1: acquire right fork, then left fork, eat, release.  *)
(***************************************************************************)

l0(self) == /\ pc[self] = "l0"
            /\ sem[Right(self)] = 1
            /\ sem' = [sem EXCEPT ![Right(self)] = 0]
            /\ pc' = [pc EXCEPT ![self] = "l1"]

l1(self) == /\ pc[self] = "l1"
            /\ sem[Left(self)] = 1
            /\ sem' = [sem EXCEPT ![Left(self)] = 0]
            /\ pc' = [pc EXCEPT ![self] = "eat"]

eat(self) == /\ pc[self] = "eat"
             /\ sem' = [sem EXCEPT ![Left(self)] = 1, ![Right(self)] = 1]
             /\ pc' = [pc EXCEPT ![self] = "l0"]

Phil(self) == l0(self) \/ l1(self) \/ eat(self)

(***************************************************************************)
(* Philosopher 0: acquire left fork, then right fork, eat, release.        *)
(***************************************************************************)

m0(self) == /\ pc[self] = "l0"
            /\ sem[Left(self)] = 1
            /\ sem' = [sem EXCEPT ![Left(self)] = 0]
            /\ pc' = [pc EXCEPT ![self] = "l1"]

m1(self) == /\ pc[self] = "l1"
            /\ sem[Right(self)] = 1
            /\ sem' = [sem EXCEPT ![Right(self)] = 0]
            /\ pc' = [pc EXCEPT ![self] = "eat"]

meat(self) == /\ pc[self] = "eat"
              /\ sem' = [sem EXCEPT ![Left(self)] = 1, ![Right(self)] = 1]
              /\ pc' = [pc EXCEPT ![self] = "l0"]

LPhil(self) == m0(self) \/ m1(self) \/ meat(self)

Next == \/ (\E self \in 1..N-1 : Phil(self))
        \/ LPhil(0)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in 1..N-1 : SF_vars(Phil(self))
        /\ SF_vars(LPhil(0))

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)

TypeOK == /\ sem \in [0..N-1 -> {0, 1}]
          /\ pc \in [ProcSet -> {"l0", "l1", "eat"}]

Eating(i) == pc[i] = "eat"

(* Adjacent philosophers never eat at the same time. *)
NoAdjacentEating == \A i \in ProcSet : ~(Eating(i) /\ Eating((i + 1) % N))

(* Every philosopher eats infinitely often. *)
StarvationFree == \A i \in ProcSet : []<>Eating(i)

THEOREM Spec => [](TypeOK /\ NoAdjacentEating)
THEOREM Spec => StarvationFree

==================================================================================