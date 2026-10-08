---- MODULE DiningPhilosophers ----
EXTENDS Naturals

CONSTANT N

VARIABLES sem, pc

Proc == 0..(N - 1)

Right(i) == i
Left(i)  == IF i = 0 THEN N - 1 ELSE i - 1
Succ(i)  == IF i = N - 1 THEN 0 ELSE i + 1

Fork1(i) == IF i = 0 THEN Left(i)  ELSE Right(i)
Fork2(i) == IF i = 0 THEN Right(i) ELSE Left(i)

Init ==
  /\ sem = [k \in Proc |-> 1]
  /\ pc  = [i \in Proc |-> "acq1"]

Acquire1(i) ==
  /\ i \in Proc
  /\ pc[i] = "acq1"
  /\ sem[Fork1(i)] = 1
  /\ sem' = [sem EXCEPT ![Fork1(i)] = 0]
  /\ pc'  = [pc  EXCEPT ![i] = "acq2"]

Acquire2(i) ==
  /\ i \in Proc
  /\ pc[i] = "acq2"
  /\ sem[Fork2(i)] = 1
  /\ sem' = [sem EXCEPT ![Fork2(i)] = 0]
  /\ pc'  = [pc  EXCEPT ![i] = "eat"]

FinishEat(i) ==
  /\ i \in Proc
  /\ pc[i] = "eat"
  /\ UNCHANGED sem
  /\ pc' = [pc EXCEPT ![i] = "rel1"]

Release1(i) ==
  /\ i \in Proc
  /\ pc[i] = "rel1"
  /\ sem[Fork1(i)] = 0
  /\ sem' = [sem EXCEPT ![Fork1(i)] = 1]
  /\ pc'  = [pc  EXCEPT ![i] = "rel2"]

Release2(i) ==
  /\ i \in Proc
  /\ pc[i] = "rel2"
  /\ sem[Fork2(i)] = 0
  /\ sem' = [sem EXCEPT ![Fork2(i)] = 1]
  /\ pc'  = [pc  EXCEPT ![i] = "acq1"]

NextProc(i) ==
  Acquire1(i) \/ Acquire2(i) \/ FinishEat(i) \/ Release1(i) \/ Release2(i)

Next == \E i \in Proc: NextProc(i)

vars == << sem, pc >>

Spec ==
  Init
  /\ [][Next]_vars
  /\ \A i \in Proc: SF_vars(NextProc(i))

Invariant ==
  \A i \in Proc:
    ~(pc[i] = "eat" /\ pc[Succ(i)] = "eat")

StarvationFree ==
  \A i \in Proc: []<>(pc[i] = "eat")

====