---- MODULE DiningPhilosophers ----
EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat /\ N >= 2

(*
  N philosophers (0..N-1) sit around a table with N forks (also 0..N-1).
  Philosopher i's left fork = i, right fork = (i+1) mod N.
  Philosophers 1..N-1 acquire right then left; philosopher 0 acquires left then right.
*)

VARIABLES pc, sem

Idx == 0..(N-1)
Forks == Idx

Right(i) == IF i = N - 1 THEN 0 ELSE i + 1

LeftFork(i)  == i
RightFork(i) == Right(i)

FirstFork(i)  == IF i = 0 THEN LeftFork(i)  ELSE RightFork(i)
SecondFork(i) == IF i = 0 THEN RightFork(i) ELSE LeftFork(i)

vars == << pc, sem >>

Init ==
  /\ pc  = [ i \in Idx |-> "think" ]
  /\ sem = [ f \in Forks |-> 1 ]

Think(i) ==
  /\ i \in Idx
  /\ pc[i] = "think"
  /\ pc'   = [pc EXCEPT ![i] = "take1"]
  /\ UNCHANGED sem

Take1(i) ==
  /\ i \in Idx
  /\ pc[i] = "take1"
  /\ sem[FirstFork(i)] = 1
  /\ pc'   = [pc EXCEPT ![i] = "take2"]
  /\ sem'  = [sem EXCEPT ![FirstFork(i)] = 0]

Take2(i) ==
  /\ i \in Idx
  /\ pc[i] = "take2"
  /\ sem[SecondFork(i)] = 1
  /\ pc'   = [pc EXCEPT ![i] = "eat"]
  /\ sem'  = [sem EXCEPT ![SecondFork(i)] = 0]

EatStep(i) ==
  /\ i \in Idx
  /\ pc[i] = "eat"
  /\ pc'   = [pc EXCEPT ![i] = "put1"]
  /\ UNCHANGED sem

Put1(i) ==
  /\ i \in Idx
  /\ pc[i] = "put1"
  /\ pc'   = [pc EXCEPT ![i] = "put2"]
  /\ sem'  = [sem EXCEPT ![SecondFork(i)] = 1]

Put2(i) ==
  /\ i \in Idx
  /\ pc[i] = "put2"
  /\ pc'   = [pc EXCEPT ![i] = "think"]
  /\ sem'  = [sem EXCEPT ![FirstFork(i)] = 1]

Step(i) ==
  Think(i) \/ Take1(i) \/ Take2(i) \/ EatStep(i) \/ Put1(i) \/ Put2(i)

Next ==
  \E i \in Idx: Step(i)

Eating(i) == pc[i] = "eat"

NoAdjacentEating ==
  \A i \in Idx: ~(Eating(i) /\ Eating(Right(i)))

StarvationFreedom ==
  \A i \in Idx: []<>(Eating(i))

TypeInv ==
  /\ sem \in [Forks -> {0,1}]
  /\ pc  \in [Idx -> {"think","take1","take2","eat","put1","put2"}]

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A i \in Idx: SF_vars(Step(i))

====