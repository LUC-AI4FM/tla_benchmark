---- MODULE DiningPhilosophers ----
EXTENDS Integers, TLC, FiniteSets

CONSTANT N
ASSUME N \in 1..Nat

VARIABLES pc, sem

Phils == 0..(N-1)
Forks == 0..(N-1)
PCStates == {"L1", "L2", "L3", "L4", "L5"}

vars == <<pc, sem>>

Left(i) == i
Right(i) == (i - 1 + N) % N

FirstFork(i) == IF i = 0 THEN Left(i) ELSE Right(i)
SecondFork(i) == IF i = 0 THEN Right(i) ELSE Left(i)

TypeOK ==
  /\ pc \in [Phils -> PCStates]
  /\ sem \in [Forks -> {0, 1}]

Init ==
  /\ pc = [i \in Phils |-> "L1"]
  /\ sem = [i \in Forks |-> 1]

TryToEat(i) ==
  /\ pc[i] = "L1"
  /\ pc' = [pc EXCEPT ![i] = "L2"]
  /\ UNCHANGED sem

GetFirstFork(i) ==
  /\ pc[i] = "L2"
  /\ sem[FirstFork(i)] = 1
  /\ pc' = [pc EXCEPT ![i] = "L3"]
  /\ sem' = [sem EXCEPT ![FirstFork(i)] = 0]

GetSecondFork(i) ==
  /\ pc[i] = "L3"
  /\ sem[SecondFork(i)] = 1
  /\ pc' = [pc EXCEPT ![i] = "L4"]
  /\ sem' = [sem EXCEPT ![SecondFork(i)] = 0]

StartThinking(i) ==
  /\ pc[i] = "L4"
  /\ pc' = [pc EXCEPT ![i] = "L5"]
  /\ UNCHANGED sem

ReleaseForks(i) ==
  /\ pc[i] = "L5"
  /\ pc' = [pc EXCEPT ![i] = "L1"]
  /\ sem' = [sem EXCEPT ![Left(i)] = 1, ![Right(i)] = 1]

Phil(i) ==
  \/ TryToEat(i)
  \/ GetFirstFork(i)
  \/ GetSecondFork(i)
  \/ StartThinking(i)
  \/ ReleaseForks(i)

Next == \E i \in Phils : Phil(i)

Fairness == \A i \in Phils : SF_vars(Phil(i))

Spec == Init /\ [][Next]_vars /\ Fairness

Mutex == \A i \in Phils : ~(pc[i] = "L4" /\ pc[(i+1)%N] = "L4")

Liveness == \A i \in Phils : []<>(pc[i] = "L4")

=============================================================================