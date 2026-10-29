------------------------------ MODULE DiningPhilosophers ------------------------------
EXTENDS Naturals, TLC

CONSTANT N

ASSUME N \in Nat /\ N >= 2

Procs == 0..(N-1)

\* Fork p lies between philosopher p and philosopher (p+1) % N.
RightFork(p) == p
LeftFork(p)  == (p + 1) % N

(* --algorithm DiningPhilosophers
variables sem = [f \in Procs |-> 1];

process Philosopher \in Procs
begin
  l0: if self = 0 then
          await sem[LeftFork(self)] = 1;
          sem[LeftFork(self)] := 0;
      else
          await sem[RightFork(self)] = 1;
          sem[RightFork(self)] := 0;
      end if;
  l1: if self = 0 then
          await sem[RightFork(self)] = 1;
          sem[RightFork(self)] := 0;
      else
          await sem[LeftFork(self)] = 1;
          sem[LeftFork(self)] := 0;
      end if;
  e:  sem := [sem EXCEPT ![LeftFork(self)] = 1, ![RightFork(self)] = 1];
      goto l0;
end process
end algorithm *)

\* BEGIN TRANSLATION
VARIABLES sem, pc

vars == << sem, pc >>

ProcSet == Procs

Init == /\ sem = [f \in Procs |-> 1]
        /\ pc = [self \in ProcSet |-> "l0"]

l0(self) == /\ pc[self] = "l0"
            /\ IF self = 0
                  THEN /\ sem[LeftFork(self)] = 1
                       /\ sem' = [sem EXCEPT ![LeftFork(self)] = 0]
                  ELSE /\ sem[RightFork(self)] = 1
                       /\ sem' = [sem EXCEPT ![RightFork(self)] = 0]
            /\ pc' = [pc EXCEPT ![self] = "l1"]

l1(self) == /\ pc[self] = "l1"
            /\ IF self = 0
                  THEN /\ sem[RightFork(self)] = 1
                       /\ sem' = [sem EXCEPT ![RightFork(self)] = 0]
                  ELSE /\ sem[LeftFork(self)] = 1
                       /\ sem' = [sem EXCEPT ![LeftFork(self)] = 0]
            /\ pc' = [pc EXCEPT ![self] = "e"]

e(self) == /\ pc[self] = "e"
           /\ sem' = [sem EXCEPT ![LeftFork(self)] = 1, ![RightFork(self)] = 1]
           /\ pc' = [pc EXCEPT ![self] = "l0"]

Philosopher(self) == l0(self) \/ l1(self) \/ e(self)

Next == \E self \in Procs : Philosopher(self)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : SF_vars(Philosopher(self))
\* END TRANSLATION

TypeOK == /\ sem \in [Procs -> {0, 1}]
          /\ pc \in [Procs -> {"l0", "l1", "e"}]

\* Adjacent philosophers never eat at the same time.
NoAdjacentEating ==
    \A p \in Procs : ~(pc[p] = "e" /\ pc[(p + 1) % N] = "e")

\* Every philosopher eats infinitely often.
StarvationFree == \A p \in Procs : []<>(pc[p] = "e")

THEOREM Spec => [](TypeOK /\ NoAdjacentEating)
THEOREM Spec => StarvationFree
=======================================================================================