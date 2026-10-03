----------------------------- MODULE DiningPhilosophers -----------------------------
EXTENDS Naturals, Integers

CONSTANT N

ASSUME N \in Nat /\ N >= 2

(*
Dining philosophers with N philosophers in a ring.
Philosophers 1..N-1 acquire their right fork first, then their left.
Philosopher 0 acquires left first, then right, to break symmetry.
Forks are modeled as a semaphore-like array: 1 = available, 0 = held.
*)

Philosophers == 0 .. (N - 1)
Forks        == 0 .. (N - 1)

Left(i)  == i
Right(i) == (i + 1) % N

FirstFork(i)  == IF i = 0 THEN Left(i)  ELSE Right(i)
SecondFork(i) == IF i = 0 THEN Right(i) ELSE Left(i)

VARIABLES pc, sem
vars == << pc, sem >>

Init ==
  /\ pc = [ i \in Philosophers |-> "think" ]
  /\ sem = [ f \in Forks        |-> 1 ]

StartTry(i) ==
  /\ i \in Philosophers
  /\ pc[i] = "think"
  /\ pc' = [pc EXCEPT ![i] = "getFirst"]
  /\ UNCHANGED sem

AcquireFirst(i) ==
  /\ i \in Philosophers
  /\ pc[i] = "getFirst"
  /\ sem[FirstFork(i)] = 1
  /\ pc'  = [pc  EXCEPT ![i] = "getSecond"]
  /\ sem' = [sem EXCEPT ![FirstFork(i)] = 0]

AcquireSecond(i) ==
  /\ i \in Philosophers
  /\ pc[i] = "getSecond"
  /\ sem[SecondFork(i)] = 1
  /\ pc'  = [pc  EXCEPT ![i] = "eat"]
  /\ sem' = [sem EXCEPT ![SecondFork(i)] = 0]

BeginEat(i) ==
  /\ i \in Philosophers
  /\ pc[i] = "eat"
  /\ pc' = [pc EXCEPT ![i] = "putSecond"]
  /\ UNCHANGED sem

PutSecond(i) ==
  /\ i \in Philosophers
  /\ pc[i] = "putSecond"
  /\ pc'  = [pc  EXCEPT ![i] = "putFirst"]
  /\ sem' = [sem EXCEPT ![SecondFork(i)] = 1]

PutFirst(i) ==
  /\ i \in Philosophers
  /\ pc[i] = "putFirst"
  /\ pc'  = [pc  EXCEPT ![i] = "think"]
  /\ sem' = [sem EXCEPT ![FirstFork(i)] = 1]

Step(i) ==
  StartTry(i) \/ AcquireFirst(i) \/ AcquireSecond(i)
  \/ BeginEat(i) \/ PutSecond(i) \/ PutFirst(i)

Next ==
  \E i \in Philosophers: Step(i)

TypeOK ==
  /\ pc \in [ Philosophers -> {"think","getFirst","getSecond","eat","putSecond","putFirst"} ]
  /\ sem \in [ Forks -> {0,1} ]

MutualExclusion ==
  \A i \in Philosophers:
    ~(pc[i] = "eat" /\ pc[(i + 1) % N] = "eat")

Invariant == TypeOK /\ MutualExclusion

StarvationFreedom ==
  \A i \in Philosophers:
    [] (pc[i] = "getSecond" => <> (pc[i] = "eat"))

Spec ==
  Init /\ [][Next]_vars /\ (\A i \in Philosophers: SF_vars(Step(i)))

=============================================================================