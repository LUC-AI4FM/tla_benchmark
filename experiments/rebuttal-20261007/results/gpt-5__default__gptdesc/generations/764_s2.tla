------------------------------ MODULE DiningPhilosophers ------------------------------

EXTENDS Naturals, TLC

CONSTANT N

ASSUME N \in Nat \ {0, 1}

(*
  Philosophers are identified by Proc = 0..(N-1), arranged on a ring.
  Fork i lies between philosophers i and (i+1) % N.
  Philosopher i's right fork is Right(i) = i, and left fork is Left(i) = (i-1) % N.
  sem[f] = TRUE means fork f is available; FALSE means held by some philosopher.
  pc[i] is the control-state (program counter) of philosopher i.
  To break symmetry and avoid deadlock:
    - For i = 0: acquire left then right.
    - For i in 1..N-1: acquire right then left.
*)

Proc == 0..(N-1)

Right(i) == i
Left(i)  == (i - 1) % N

Labels == {"think", "t1", "t2", "eat", "p1", "p2"}

VARIABLES sem, pc

vars == << sem, pc >>

Init ==
  /\ sem = [f \in Proc |-> TRUE]
  /\ pc  = [i \in Proc |-> "think"]

Start(i) ==
  /\ i \in Proc
  /\ pc[i] = "think"
  /\ pc' = [pc EXCEPT ![i] = "t1"]
  /\ UNCHANGED sem

Acq1(i) ==
  /\ i \in Proc
  /\ pc[i] = "t1"
  /\ IF i = 0
        THEN /\ sem[Left(i)] = TRUE
             /\ sem' = [sem EXCEPT ![Left(i)] = FALSE]
        ELSE /\ sem[Right(i)] = TRUE
             /\ sem' = [sem EXCEPT ![Right(i)] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "t2"]

Acq2(i) ==
  /\ i \in Proc
  /\ pc[i] = "t2"
  /\ IF i = 0
        THEN /\ sem[Right(i)] = TRUE
             /\ sem' = [sem EXCEPT ![Right(i)] = FALSE]
        ELSE /\ sem[Left(i)] = TRUE
             /\ sem' = [sem EXCEPT ![Left(i)] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "eat"]

EatStep(i) ==
  /\ i \in Proc
  /\ pc[i] = "eat"
  /\ pc' = [pc EXCEPT ![i] = "p1"]
  /\ UNCHANGED sem

Rel1(i) ==
  /\ i \in Proc
  /\ pc[i] = "p1"
  /\ IF i = 0
        THEN sem' = [sem EXCEPT ![Left(i)] = TRUE]
        ELSE sem' = [sem EXCEPT ![Right(i)] = TRUE]
  /\ pc' = [pc EXCEPT ![i] = "p2"]

Rel2(i) ==
  /\ i \in Proc
  /\ pc[i] = "p2"
  /\ IF i = 0
        THEN sem' = [sem EXCEPT ![Right(i)] = TRUE]
        ELSE sem' = [sem EXCEPT ![Left(i)] = TRUE]
  /\ pc' = [pc EXCEPT ![i] = "think"]

ProcNext(i) ==
  Start(i) \/ Acq1(i) \/ Acq2(i) \/ EatStep(i) \/ Rel1(i) \/ Rel2(i)

Next ==
  \E i \in Proc: ProcNext(i)

Spec ==
  Init /\ [][Next]_vars /\ \A i \in Proc: SF_vars(ProcNext(i))

TypeInvariant ==
  /\ sem \in [Proc -> BOOLEAN]
  /\ pc \in [Proc -> Labels]

NoAdjacentEat ==
  \A i \in Proc: ~(pc[i] = "eat" /\ pc[(i + 1) % N] = "eat")

Invariant == TypeInvariant /\ NoAdjacentEat

StarvationFreedom ==
  \A i \in Proc: []<>(pc[i] = "eat")

=============================================================================