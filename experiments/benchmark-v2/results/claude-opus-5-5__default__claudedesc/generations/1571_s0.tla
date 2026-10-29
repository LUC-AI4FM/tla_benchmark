------------------------------ MODULE DiningPhilosophers ------------------------------
EXTENDS Integers, TLC

CONSTANT N

ASSUME N \in Nat /\ N >= 2

Procs == 0..(N-1)

LeftFork(i)  == i
RightFork(i) == (i + 1) % N

VARIABLES sem, pc

vars == << sem, pc >>

Init == /\ sem = [f \in Procs |-> 1]
        /\ pc  = [i \in Procs |-> IF i = 0 THEN "l01" ELSE "l1"]

TypeOK == /\ sem \in [Procs -> {0, 1}]
          /\ pc \in [Procs -> {"l1", "l2", "l3", "l4", "l01", "l02", "l03", "l04"}]

(***************************************************************************)
(* Philosophers 1..N-1: right fork first, then left fork.                  *)
(***************************************************************************)
l1(self) == /\ pc[self] = "l1"
            /\ sem[RightFork(self)] = 1
            /\ sem' = [sem EXCEPT ![RightFork(self)] = 0]
            /\ pc' = [pc EXCEPT ![self] = "l2"]

l2(self) == /\ pc[self] = "l2"
            /\ sem[LeftFork(self)] = 1
            /\ sem' = [sem EXCEPT ![LeftFork(self)] = 0]
            /\ pc' = [pc EXCEPT ![self] = "l3"]

\* eat, then release right fork
l3(self) == /\ pc[self] = "l3"
            /\ sem' = [sem EXCEPT ![RightFork(self)] = 1]
            /\ pc' = [pc EXCEPT ![self] = "l4"]

\* release left fork
l4(self) == /\ pc[self] = "l4"
            /\ sem' = [sem EXCEPT ![LeftFork(self)] = 1]
            /\ pc' = [pc EXCEPT ![self] = "l1"]

Proc(self) == l1(self) \/ l2(self) \/ l3(self) \/ l4(self)

(***************************************************************************)
(* Philosopher 0: left fork first, then right fork.                        *)
(***************************************************************************)
l01 == /\ pc[0] = "l01"
       /\ sem[LeftFork(0)] = 1
       /\ sem' = [sem EXCEPT ![LeftFork(0)] = 0]
       /\ pc' = [pc EXCEPT ![0] = "l02"]

l02 == /\ pc[0] = "l02"
       /\ sem[RightFork(0)] = 1
       /\ sem' = [sem EXCEPT ![RightFork(0)] = 0]
       /\ pc' = [pc EXCEPT ![0] = "l03"]

\* eat, then release right fork
l03 == /\ pc[0] = "l03"
       /\ sem' = [sem EXCEPT ![RightFork(0)] = 1]
       /\ pc' = [pc EXCEPT ![0] = "l04"]

\* release left fork
l04 == /\ pc[0] = "l04"
       /\ sem' = [sem EXCEPT ![LeftFork(0)] = 1]
       /\ pc' = [pc EXCEPT ![0] = "l01"]

Proc0 == l01 \/ l02 \/ l03 \/ l04

Next == Proc0 \/ (\E self \in 1..(N-1) : Proc(self))

Spec == /\ Init
        /\ [][Next]_vars
        /\ SF_vars(Proc0)
        /\ \A self \in 1..(N-1) : SF_vars(Proc(self))

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
Eating(i) == IF i = 0 THEN pc[0] = "l03" ELSE pc[i] = "l3"

Invariant == \A i \in Procs : ~(Eating(i) /\ Eating((i + 1) % N))

StarvationFree == \A i \in Procs : []<>Eating(i)

=======================================================================================