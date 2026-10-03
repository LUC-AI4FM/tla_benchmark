---- MODULE DiningPhilosophers ----
EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat /\ N >= 2

VARIABLES pc, forks

Phils == 0..(N - 1)
ForkIdx == Phils

Left(i) == i
Right(i) == IF i = N - 1 THEN 0 ELSE i + 1

FirstFork(i) == IF i = 0 THEN Left(i) ELSE Right(i)
SecondFork(i) == IF i = 0 THEN Right(i) ELSE Left(i)

Init ==
  /\ pc = [i \in Phils |-> "think"]
  /\ forks = [k \in ForkIdx |-> 1]

ThinkToGet1(i) ==
  /\ i \in Phils
  /\ pc[i] = "think"
  /\ pc' = [pc EXCEPT ![i] = "get1"]
  /\ UNCHANGED forks

Get1(i) ==
  LET f == FirstFork(i) IN
  /\ i \in Phils
  /\ pc[i] = "get1"
  /\ forks[f] = 1
  /\ pc' = [pc EXCEPT ![i] = "get2"]
  /\ forks' = [forks EXCEPT ![f] = 0]

Get2(i) ==
  LET f == SecondFork(i) IN
  /\ i \in Phils
  /\ pc[i] = "get2"
  /\ forks[f] = 1
  /\ pc' = [pc EXCEPT ![i] = "eat"]
  /\ forks' = [forks EXCEPT ![f] = 0]

EatToPut1(i) ==
  /\ i \in Phils
  /\ pc[i] = "eat"
  /\ pc' = [pc EXCEPT ![i] = "put1"]
  /\ UNCHANGED forks

Put1(i) ==
  LET f == FirstFork(i) IN
  /\ i \in Phils
  /\ pc[i] = "put1"
  /\ forks[f] = 0
  /\ pc' = [pc EXCEPT ![i] = "put2"]
  /\ forks' = [forks EXCEPT ![f] = 1]

Put2(i) ==
  LET f == SecondFork(i) IN
  /\ i \in Phils
  /\ pc[i] = "put2"
  /\ forks[f] = 0
  /\ pc' = [pc EXCEPT ![i] = "think"]
  /\ forks' = [forks EXCEPT ![f] = 1]

PStep(i) ==
  ThinkToGet1(i) \/
  Get1(i) \/
  Get2(i) \/
  EatToPut1(i) \/
  Put1(i) \/
  Put2(i)

Next ==
  \E i \in Phils : PStep(i)

vars == << pc, forks >>

Eating(i) == pc[i] = "eat"

MutualExclusion ==
  \A i \in Phils : ~(Eating(i) /\ Eating(Right(i)))

StarvationFreedom ==
  \A i \in Phils : []<>(Eating(i))

Spec ==
  Init /\ [][Next]_vars /\ \A i \in Phils : SF_vars(PStep(i))
====