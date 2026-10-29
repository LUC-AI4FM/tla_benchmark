------------------------- MODULE DiningPhilosophers -------------------------
(***************************************************************************)
(* Dining Philosophers for N philosophers arranged in a ring.              *)
(* sem[f] = 1 iff fork f is available.                                     *)
(* Philosopher i's right fork is fork i and its left fork is fork          *)
(* (i+1) % N.  Philosophers 1..N-1 acquire the right fork first and then   *)
(* the left fork.  Philosopher 0 acquires the left fork first and then the *)
(* right fork.  This asymmetry breaks the circular wait and so prevents    *)
(* deadlock.                                                               *)
(***************************************************************************)
EXTENDS Naturals, TLC

CONSTANT N

ASSUME N \in Nat /\ N >= 2

(* --algorithm DiningPhilosophers
variables sem = [f \in 0..(N-1) |-> 1];
fair+ process Proc \in 0..(N-1)
begin
l1: while TRUE do
l2:   await sem[First(self)] = 1;
      sem[First(self)] := 0;
l3:   await sem[Second(self)] = 1;
      sem[Second(self)] := 0;
e:    sem[First(self)] := 1 || sem[Second(self)] := 1;
    end while;
end process;
end algorithm *)

\* BEGIN TRANSLATION
VARIABLES sem, pc

vars == << sem, pc >>

ProcSet == 0..(N-1)

Forks == 0..(N-1)

RightFork(i) == i
LeftFork(i)  == (i + 1) % N

First(i)  == IF i = 0 THEN LeftFork(i)  ELSE RightFork(i)
Second(i) == IF i = 0 THEN RightFork(i) ELSE LeftFork(i)

Init == /\ sem = [f \in Forks |-> 1]
        /\ pc = [self \in ProcSet |-> "l1"]

l1(self) == /\ pc[self] = "l1"
            /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ UNCHANGED sem

l2(self) == /\ pc[self] = "l2"
            /\ sem[First(self)] = 1
            /\ sem' = [sem EXCEPT ![First(self)] = 0]
            /\ pc' = [pc EXCEPT ![self] = "l3"]

l3(self) == /\ pc[self] = "l3"
            /\ sem[Second(self)] = 1
            /\ sem' = [sem EXCEPT ![Second(self)] = 0]
            /\ pc' = [pc EXCEPT ![self] = "e"]

e(self) == /\ pc[self] = "e"
           /\ sem' = [sem EXCEPT ![First(self)] = 1, ![Second(self)] = 1]
           /\ pc' = [pc EXCEPT ![self] = "l1"]

Proc(self) == l1(self) \/ l2(self) \/ l3(self) \/ e(self)

Next == \E self \in 0..(N-1) : Proc(self)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in 0..(N-1) : SF_vars(Proc(self))
\* END TRANSLATION

-----------------------------------------------------------------------------

TypeOK == /\ sem \in [Forks -> {0, 1}]
          /\ pc \in [ProcSet -> {"l1", "l2", "l3", "e"}]

(* Adjacent philosophers never eat at the same time. *)
Invariant == \A i \in ProcSet : ~(pc[i] = "e" /\ pc[(i + 1) % N] = "e")

(* Every philosopher eats infinitely often. *)
StarvationFree == \A i \in ProcSet : []<>(pc[i] = "e")

THEOREM Spec => [](TypeOK /\ Invariant)
THEOREM Spec => StarvationFree
=============================================================================