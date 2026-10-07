--------------------------- MODULE DiningPhilosophersAsymmetric ---------------------------

EXTENDS Naturals, TLC

CONSTANT N

ASSUME N \in Nat /\ N >= 2

VARIABLES sem, pc

P == 0..(N-1)

Left(i)  == i
Right(i) == IF i = N-1 THEN 0 ELSE i + 1

StartLabel(i)   == IF i = 0 THEN "l01" ELSE "l1"
AfterFirst(i)   == IF i = 0 THEN "l02" ELSE "l2"
EatLabel(i)     == IF i = 0 THEN "l03" ELSE "l3"
ReleaseLabel(i) == IF i = 0 THEN "l04" ELSE "l4"

FirstFork(i)  == IF i = 0 THEN Left(i)  ELSE Right(i)
SecondFork(i) == IF i = 0 THEN Right(i) ELSE Left(i)

vars == << sem, pc >>

Init ==
  /\ sem \in [P -> {0, 1}]
  /\ sem = [j \in P |-> 1]
  /\ pc \in [P -> {"l1","l2","l3","l4","l01","l02","l03","l04"}]
  /\ pc = [i \in P |-> StartLabel(i)]

AcquireFirst(i) ==
  /\ i \in P
  /\ IF i = 0
        THEN /\ pc[i] = "l01"
             /\ sem[Left(i)] = 1
             /\ sem' = [sem EXCEPT ![Left(i)] = 0]
             /\ pc'  = [pc  EXCEPT ![i]       = "l02"]
        ELSE /\ pc[i] = "l1"
             /\ sem[Right(i)] = 1
             /\ sem' = [sem EXCEPT ![Right(i)] = 0]
             /\ pc'  = [pc  EXCEPT ![i]        = "l2"]

AcquireSecond(i) ==
  /\ i \in P
  /\ IF i = 0
        THEN /\ pc[i] = "l02"
             /\ sem[Right(i)] = 1
             /\ sem' = [sem EXCEPT ![Right(i)] = 0]
             /\ pc'  = [pc  EXCEPT ![i]        = "l03"]
        ELSE /\ pc[i] = "l2"
             /\ sem[Left(i)] = 1
             /\ sem' = [sem EXCEPT ![Left(i)] = 0]
             /\ pc'  = [pc  EXCEPT ![i]       = "l3"]

EatToReleaseRight(i) ==
  /\ i \in P
  /\ IF i = 0
        THEN /\ pc[i] = "l03"
             /\ sem' = [sem EXCEPT ![Right(i)] = 1]
             /\ pc'  = [pc  EXCEPT ![i]        = "l04"]
        ELSE /\ pc[i] = "l3"
             /\ sem' = [sem EXCEPT ![Right(i)] = 1]
             /\ pc'  = [pc  EXCEPT ![i]        = "l4"]

ReleaseLeftAndRestart(i) ==
  /\ i \in P
  /\ IF i = 0
        THEN /\ pc[i] = "l04"
             /\ sem' = [sem EXCEPT ![Left(i)] = 1]
             /\ pc'  = [pc  EXCEPT ![i]       = "l01"]
        ELSE /\ pc[i] = "l4"
             /\ sem' = [sem EXCEPT ![Left(i)] = 1]
             /\ pc'  = [pc  EXCEPT ![i]       = "l1"]

Step(i) ==
  AcquireFirst(i) \/
  AcquireSecond(i) \/
  EatToReleaseRight(i) \/
  ReleaseLeftAndRestart(i)

Next ==
  \E i \in P: Step(i)

Fairness ==
  \A i \in P: SF_vars(Step(i))

Spec ==
  Init /\ [][Next]_vars /\ Fairness

Eating(i) == IF i = 0 THEN pc[i] = "l03" ELSE pc[i] = "l3"

Invariant ==
  \A i \in P: ~(Eating(i) /\ Eating(Right(i)))

StarvationFree ==
  \A i \in P: [](<>Eating(i))

=============================================================================