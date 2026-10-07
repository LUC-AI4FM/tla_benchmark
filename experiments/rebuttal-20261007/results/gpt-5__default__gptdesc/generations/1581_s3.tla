------------------------------ MODULE DiningPhilosophers ------------------------------

EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat \ {0}

VARIABLES pc, sem

ProcSet == 0..(N - 1)
Forks   == ProcSet

LFork(i) == i
RFork(i) == IF i = 0 THEN N - 1 ELSE i - 1

Succ(i) == IF i = N - 1 THEN 0 ELSE i + 1

FirstFork(i)  == IF i = 0 THEN LFork(i) ELSE RFork(i)
SecondFork(i) == IF i = 0 THEN RFork(i) ELSE LFork(i)

Init ==
  /\ pc  = [i \in ProcSet |-> "thinking"]
  /\ sem = [f \in Forks   |-> TRUE]

Think(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "thinking"
  /\ pc' = [pc EXCEPT ![i] = "acq1"]
  /\ UNCHANGED sem

TakeFirst(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "acq1"
  /\ sem[FirstFork(i)] = TRUE
  /\ sem' = [sem EXCEPT ![FirstFork(i)] = FALSE]
  /\ pc'  = [pc  EXCEPT ![i] = "acq2"]

TakeSecond(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "acq2"
  /\ sem[SecondFork(i)] = TRUE
  /\ sem' = [sem EXCEPT ![SecondFork(i)] = FALSE]
  /\ pc'  = [pc  EXCEPT ![i] = "eating"]

Release(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "eating"
  /\ sem' = [sem EXCEPT ![LFork(i)] = TRUE, ![RFork(i)] = TRUE]
  /\ pc'  = [pc  EXCEPT ![i] = "thinking"]

P(i) == Think(i) \/ TakeFirst(i) \/ TakeSecond(i) \/ Release(i)

Next == \E i \in ProcSet : P(i)

vars == << pc, sem >>

Spec == Init /\ [][Next]_vars /\ \A i \in ProcSet : SF_vars(P(i))

NoAdjacentEating ==
  \A i \in ProcSet :
    ~(pc[i] = "eating" /\ pc[Succ(i)] = "eating")

StarvationFreedom ==
  \A i \in ProcSet : []<>(pc[i] = "eating")

=============================================================================