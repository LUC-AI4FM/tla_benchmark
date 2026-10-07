------------------------------ MODULE DiningPhilosophers ------------------------------

EXTENDS Naturals, TLC

CONSTANT N

ASSUME N \in Nat /\ N >= 2

(*
  Philosophers and forks are indexed 0..N-1 arranged in a ring.
  Fork i lies between philosopher i and philosopher (i+1) mod N.
*)

Philos == 0..(N - 1)
Forks  == 0..(N - 1)

Succ(i) == IF i = N - 1 THEN 0 ELSE i + 1

Left(i)  == i
Right(i) == Succ(i)

(*
  Asymmetric acquisition order:
  - Philosopher 0: left then right.
  - Philosophers 1..N-1: right then left.
*)
FirstFork(i)  == IF i = 0 THEN Left(i)  ELSE Right(i)
SecondFork(i) == IF i = 0 THEN Right(i) ELSE Left(i)

STATES == {"think", "take2", "eat", "put2", "put1"}

VARIABLES pc, sem

vars == << pc, sem >>

Init ==
  /\ pc  = [i \in Philos |-> "think"]
  /\ sem = [f \in Forks  |-> TRUE]

TakeFirst(i) ==
  /\ i \in Philos
  /\ pc[i] = "think"
  /\ sem[FirstFork(i)] = TRUE
  /\ pc'  = [pc EXCEPT ![i] = "take2"]
  /\ sem' = [sem EXCEPT ![FirstFork(i)] = FALSE]

TakeSecond(i) ==
  /\ i \in Philos
  /\ pc[i] = "take2"
  /\ sem[SecondFork(i)] = TRUE
  /\ pc'  = [pc EXCEPT ![i] = "eat"]
  /\ sem' = [sem EXCEPT ![SecondFork(i)] = FALSE]

EatStep(i) ==
  /\ i \in Philos
  /\ pc[i] = "eat"
  /\ pc' = [pc EXCEPT ![i] = "put2"]
  /\ UNCHANGED sem

PutSecond(i) ==
  /\ i \in Philos
  /\ pc[i] = "put2"
  /\ pc'  = [pc EXCEPT ![i] = "put1"]
  /\ sem' = [sem EXCEPT ![SecondFork(i)] = TRUE]

PutFirst(i) ==
  /\ i \in Philos
  /\ pc[i] = "put1"
  /\ pc'  = [pc EXCEPT ![i] = "think"]
  /\ sem' = [sem EXCEPT ![FirstFork(i)] = TRUE]

Proc(i) == TakeFirst(i) \/ TakeSecond(i) \/ EatStep(i) \/ PutSecond(i) \/ PutFirst(i)

Next == \E i \in Philos: Proc(i)

TypeOK == pc \in [Philos -> STATES] /\ sem \in [Forks -> BOOLEAN]

(*
  Safety: adjacent philosophers never eat simultaneously.
*)
NoAdjacentEating == \A i \in Philos: ~(pc[i] = "eat" /\ pc[Succ(i)] = "eat")

(*
  Liveness: each philosopher eats infinitely often (starvation freedom).
*)
StarvationFree == \A i \in Philos: []<>(pc[i] = "eat")

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A i \in Philos: SF_vars(Proc(i))

=============================================================================