------------------------------- MODULE DiningPhilosophers -------------------------------

EXTENDS Integers

CONSTANT N

ASSUME N \in Nat /\ N >= 2

VARIABLES sem, pc

vars == <<sem, pc>>

ProcSet == 0..(N-1)

Left(i) == (i - 1) % N
Right(i) == i % N

FirstFork(i) == IF i = 0 THEN Left(i) ELSE Right(i)
SecondFork(i) == IF i = 0 THEN Right(i) ELSE Left(i)

TypeOK ==
  /\ sem \in [ProcSet -> {0, 1}]
  /\ pc \in [ProcSet -> {"think", "take1", "take2", "eat", "put2", "put1"}]

Init ==
  /\ sem = [j \in ProcSet |-> 1]
  /\ pc  = [i \in ProcSet |-> "think"]

ThinkToTake1(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "think"
  /\ pc' = [pc EXCEPT ![i] = "take1"]
  /\ UNCHANGED sem

Take1(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "take1"
  /\ sem[FirstFork(i)] = 1
  /\ sem' = [sem EXCEPT ![FirstFork(i)] = 0]
  /\ pc' = [pc EXCEPT ![i] = "take2"]

Take2(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "take2"
  /\ sem[SecondFork(i)] = 1
  /\ sem' = [sem EXCEPT ![SecondFork(i)] = 0]
  /\ pc' = [pc EXCEPT ![i] = "eat"]

EatToPut2(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "eat"
  /\ pc' = [pc EXCEPT ![i] = "put2"]
  /\ UNCHANGED sem

Put2(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "put2"
  /\ sem' = [sem EXCEPT ![SecondFork(i)] = 1]
  /\ pc' = [pc EXCEPT ![i] = "put1"]

Put1(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "put1"
  /\ sem' = [sem EXCEPT ![FirstFork(i)] = 1]
  /\ pc' = [pc EXCEPT ![i] = "think"]

Proc(i) ==
  ThinkToTake1(i)
  \/ Take1(i)
  \/ Take2(i)
  \/ EatToPut2(i)
  \/ Put2(i)
  \/ Put1(i)

Next == \E i \in ProcSet: Proc(i)

NoAdjacentEat ==
  \A i \in ProcSet:
    ~(pc[i] = "eat" /\ pc[(i + 1) % N] = "eat")

Invariant == TypeOK /\ NoAdjacentEat

StarvationFreedom ==
  \A i \in ProcSet: []<>(pc[i] = "eat")

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A i \in ProcSet: SF_vars(Proc(i))

THEOREM Spec => []Invariant

THEOREM Spec => StarvationFreedom

=============================================================================