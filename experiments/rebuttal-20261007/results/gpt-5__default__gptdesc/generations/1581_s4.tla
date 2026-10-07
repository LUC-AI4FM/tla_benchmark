----------------------------- MODULE DiningPhilosophers -----------------------------

EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat /\ N >= 2

ProcSet == 0..(N-1)
Forks   == 0..(N-1)

Left(i)  == i
Right(i) == (i - 1) \mod N

FirstFork(i)  == IF i = 0 THEN Left(i)  ELSE Right(i)
SecondFork(i) == IF i = 0 THEN Right(i) ELSE Left(i)

PCStates == {"think", "try1", "try2", "eat"}

VARIABLES pc, sem

vars == << pc, sem >>

Init ==
  /\ pc  = [i \in ProcSet |-> "think"]
  /\ sem = [f \in Forks  |-> TRUE]

Think(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "think"
  /\ pc' = [pc EXCEPT ![i] = "try1"]
  /\ UNCHANGED sem

TakeFirst(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "try1"
  /\ sem[FirstFork(i)] = TRUE
  /\ sem' = [sem EXCEPT ![FirstFork(i)] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "try2"]

TakeSecond(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "try2"
  /\ sem[SecondFork(i)] = TRUE
  /\ sem' = [sem EXCEPT ![SecondFork(i)] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "eat"]

Release(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "eat"
  /\ sem' = [sem EXCEPT ![FirstFork(i)] = TRUE, ![SecondFork(i)] = TRUE]
  /\ pc'  = [pc EXCEPT ![i] = "think"]

ProcStep(i) == Think(i) \/ TakeFirst(i) \/ TakeSecond(i) \/ Release(i)

Next == \E i \in ProcSet : ProcStep(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A i \in ProcSet : SF_vars(ProcStep(i))

Eating(i) == pc[i] = "eat"

AdjacentNoEat ==
  \A i \in ProcSet :
    ~ (Eating(i) /\ Eating((i + 1) \mod N))

StarvationFree ==
  \A i \in ProcSet : []<>(Eating(i))

================================================================================