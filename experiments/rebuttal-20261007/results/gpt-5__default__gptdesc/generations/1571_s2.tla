---- MODULE DiningPhilosophers ----
EXTENDS Naturals, TLC

CONSTANT N

ASSUME N \in Nat /\ N >= 2

(*
  N philosophers 0..N-1 around a ring.
  Fork k sits between philosophers k and (k+1) mod N.
  Philosopher i's right fork is k = i.
  Philosopher i's left fork is k = Pred(i).
  Philosophers 1..N-1 acquire right then left; philosopher 0 acquires left then right.
*)

Proc == 0..(N-1)
ForksIdx == Proc

Succ(i) == IF i = N - 1 THEN 0 ELSE i + 1
Pred(i) == IF i = 0 THEN N - 1 ELSE i - 1

Right(i) == i
Left(i)  == Pred(i)

FirstFork(i)  == IF i = 0 THEN Left(i) ELSE Right(i)
SecondFork(i) == IF i = 0 THEN Right(i) ELSE Left(i)

States == {"think", "take1", "take2", "eat", "put2", "put1"}

VARIABLES pstate, forks

vars == << pstate, forks >>

Init ==
  /\ pstate = [i \in Proc |-> "think"]
  /\ forks  = [k \in ForksIdx |-> 1]

Step(i) ==
  \/ /\ pstate[i] = "think"
     /\ pstate' = [pstate EXCEPT ![i] = "take1"]
     /\ UNCHANGED forks
  \/ /\ pstate[i] = "take1"
     /\ forks[FirstFork(i)] = 1
     /\ pstate' = [pstate EXCEPT ![i] = "take2"]
     /\ forks'  = [forks  EXCEPT ![FirstFork(i)] = 0]
  \/ /\ pstate[i] = "take2"
     /\ forks[FirstFork(i)] = 0
     /\ forks[SecondFork(i)] = 1
     /\ pstate' = [pstate EXCEPT ![i] = "eat"]
     /\ forks'  = [forks  EXCEPT ![SecondFork(i)] = 0]
  \/ /\ pstate[i] = "eat"
     /\ pstate' = [pstate EXCEPT ![i] = "put2"]
     /\ UNCHANGED forks
  \/ /\ pstate[i] = "put2"
     /\ forks[SecondFork(i)] = 0
     /\ pstate' = [pstate EXCEPT ![i] = "put1"]
     /\ forks'  = [forks  EXCEPT ![SecondFork(i)] = 1]
  \/ /\ pstate[i] = "put1"
     /\ forks[FirstFork(i)] = 0
     /\ pstate' = [pstate EXCEPT ![i] = "think"]
     /\ forks'  = [forks  EXCEPT ![FirstFork(i)] = 1]

Next == \E i \in Proc: Step(i)

Eating(i) == pstate[i] = "eat"
Hungry(i) == pstate[i] \in {"take1", "take2"}

TypeOK ==
  /\ pstate \in [Proc -> States]
  /\ forks \in [ForksIdx -> {0, 1}]

EatMutex ==
  \A i \in Proc: ~(Eating(i) /\ Eating(Succ(i)))

HoldsFirst(i)  == pstate[i] \in {"take2", "eat", "put2", "put1"}
HoldsSecond(i) == pstate[i] \in {"eat", "put2"}

ForkOwnershipOk ==
  /\ \A i \in Proc: HoldsFirst(i)  => forks[FirstFork(i)]  = 0
  /\ \A i \in Proc: HoldsSecond(i) => forks[SecondFork(i)] = 0

Inv == TypeOK /\ EatMutex /\ ForkOwnershipOk

Fairness == \A i \in Proc: SF_vars(Step(i))

Spec == Init /\ [][Next]_vars /\ Fairness

StarvationFree == \A i \in Proc: []( Hungry(i) => <> Eating(i) )

====