----------------------------- MODULE DiningPhilosophers -----------------------------

EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat /\ N >= 2

(*
  Philosophers are indexed 0..N-1 in a ring.
  Fork i sits between philosophers i and Right(i).
*)

P == 0 .. (N - 1)

Left(i)  == i
Right(i) == IF i = N - 1 THEN 0 ELSE i + 1

(*
  To avoid symmetric deadlock:
  - Philosopher 0 acquires Left then Right
  - Philosophers 1..N-1 acquire Right then Left
*)
FirstFork(i)  == IF i = 0 THEN Left(i)  ELSE Right(i)
SecondFork(i) == IF i = 0 THEN Right(i) ELSE Left(i)

VARIABLES pc, forks

vars == << pc, forks >>

Init ==
  /\ pc = [i \in P |-> "think"]
  /\ forks = [k \in P |-> 1]

StepThink(i) ==
  /\ i \in P
  /\ pc[i] = "think"
  /\ pc' = [pc EXCEPT ![i] = "acq1"]
  /\ UNCHANGED forks

StepAcq1(i) ==
  /\ i \in P
  /\ pc[i] = "acq1"
  /\ forks[FirstFork(i)] = 1
  /\ pc' = [pc EXCEPT ![i] = "acq2"]
  /\ forks' = [forks EXCEPT ![FirstFork(i)] = @ - 1]

StepAcq2(i) ==
  /\ i \in P
  /\ pc[i] = "acq2"
  /\ forks[SecondFork(i)] = 1
  /\ pc' = [pc EXCEPT ![i] = "eat"]
  /\ forks' = [forks EXCEPT ![SecondFork(i)] = @ - 1]

StepEatToRel1(i) ==
  /\ i \in P
  /\ pc[i] = "eat"
  /\ pc' = [pc EXCEPT ![i] = "rel1"]
  /\ UNCHANGED forks

StepRel1(i) ==
  /\ i \in P
  /\ pc[i] = "rel1"
  /\ forks[SecondFork(i)] = 0
  /\ pc' = [pc EXCEPT ![i] = "rel2"]
  /\ forks' = [forks EXCEPT ![SecondFork(i)] = @ + 1]

StepRel2(i) ==
  /\ i \in P
  /\ pc[i] = "rel2"
  /\ forks[FirstFork(i)] = 0
  /\ pc' = [pc EXCEPT ![i] = "think"]
  /\ forks' = [forks EXCEPT ![FirstFork(i)] = @ + 1]

PhStep(i) ==
  StepThink(i)
  \/ StepAcq1(i)
  \/ StepAcq2(i)
  \/ StepEatToRel1(i)
  \/ StepRel1(i)
  \/ StepRel2(i)

Next ==
  \E i \in P : PhStep(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A i \in P : SF_vars(PhStep(i))

(*
  Safety invariant: mutual-exclusion-style property —
  no adjacent philosophers eat simultaneously.
*)
EatingMutex ==
  \A i \in P : ~(pc[i] = "eat" /\ pc[Right(i)] = "eat")

EatingInvariant == [](EatingMutex)

(*
  Liveness: starvation-freedom — every philosopher eats infinitely often.
*)
StarvationFreedom ==
  \A i \in P : []<>(pc[i] = "eat")

=============================================================================