------------------------------ MODULE DiningPhilosophers ------------------------------

EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat /\ N >= 2

Procs == 0..(N-1)

VARIABLES pc, fork

vars == << pc, fork >>

Right(i) == i
Left(i)  == (i + N - 1) \mod N

FirstFork(i)  == IF i = 0 THEN Left(i) ELSE Right(i)
SecondFork(i) == IF i = 0 THEN Right(i) ELSE Left(i)

Init ==
  /\ pc = [i \in Procs |-> "think"]
  /\ fork = [k \in 0..(N-1) |-> 1]

ThinkToTake1(i) ==
  /\ i \in Procs
  /\ pc[i] = "think"
  /\ pc' = [pc EXCEPT ![i] = "take1"]
  /\ UNCHANGED fork

Take1Acquire(i) ==
  /\ i \in Procs
  /\ pc[i] = "take1"
  /\ fork[FirstFork(i)] = 1
  /\ fork' = [fork EXCEPT ![FirstFork(i)] = 0]
  /\ pc' = [pc EXCEPT ![i] = "take2"]

Take2Acquire(i) ==
  /\ i \in Procs
  /\ pc[i] = "take2"
  /\ fork[SecondFork(i)] = 1
  /\ fork' = [fork EXCEPT ![SecondFork(i)] = 0]
  /\ pc' = [pc EXCEPT ![i] = "eat"]

EatToPut1(i) ==
  /\ i \in Procs
  /\ pc[i] = "eat"
  /\ pc' = [pc EXCEPT ![i] = "put1"]
  /\ UNCHANGED fork

Put1Release(i) ==
  /\ i \in Procs
  /\ pc[i] = "put1"
  /\ fork[FirstFork(i)] = 0
  /\ fork' = [fork EXCEPT ![FirstFork(i)] = 1]
  /\ pc' = [pc EXCEPT ![i] = "put2"]

Put2Release(i) ==
  /\ i \in Procs
  /\ pc[i] = "put2"
  /\ fork[SecondFork(i)] = 0
  /\ fork' = [fork EXCEPT ![SecondFork(i)] = 1]
  /\ pc' = [pc EXCEPT ![i] = "think"]

Proc(i) ==
  ThinkToTake1(i)
  \/ Take1Acquire(i)
  \/ Take2Acquire(i)
  \/ EatToPut1(i)
  \/ Put1Release(i)
  \/ Put2Release(i)

Next ==
  \E i \in Procs : Proc(i)

TypeOK ==
  /\ pc \in [Procs -> {"think","take1","take2","eat","put1","put2"}]
  /\ fork \in [0..(N-1) -> {0,1}]

Eating(i) == pc[i] = "eat"
Hungry(i) == pc[i] \in {"take1","take2"}

MutualExclusion ==
  \A i \in Procs : ~(Eating(i) /\ Eating((i + 1) \mod N))

EatingHasBothForks ==
  \A i \in Procs :
    Eating(i) => /\ fork[FirstFork(i)] = 0
                 /\ fork[SecondFork(i)] = 0

Invariant == TypeOK /\ MutualExclusion /\ EatingHasBothForks

StarvationFreedom ==
  \A i \in Procs : []( Hungry(i) => <>Eating(i) )

Spec ==
  Init /\ [][Next]_vars /\ \A i \in Procs : SF_vars(Proc(i))

=============================================================================