---- MODULE DiningPhilosophers ----
EXTENDS Naturals

CONSTANT N

VARIABLES phase, forkOwner

Philosophers == 0..(N - 1)
Forks        == 0..(N - 1)

NoOwner == N

States == {"Thinking", "HasFirst", "Eating"}

Left(i)  == i
Right(i) == (i + N - 1) % N

FirstFork(i)  == IF i = 0 THEN Left(i) ELSE Right(i)
SecondFork(i) == IF i = 0 THEN Right(i) ELSE Left(i)

Init ==
  /\ phase = [i \in Philosophers |-> "Thinking"]
  /\ forkOwner = [f \in Forks |-> NoOwner]

TakeFirst(i) ==
  /\ i \in Philosophers
  /\ phase[i] = "Thinking"
  /\ forkOwner[FirstFork(i)] = NoOwner
  /\ phase'     = [phase EXCEPT ![i] = "HasFirst"]
  /\ forkOwner' = [forkOwner EXCEPT ![FirstFork(i)] = i]

TakeSecond(i) ==
  /\ i \in Philosophers
  /\ phase[i] = "HasFirst"
  /\ forkOwner[FirstFork(i)] = i
  /\ forkOwner[SecondFork(i)] = NoOwner
  /\ phase'     = [phase EXCEPT ![i] = "Eating"]
  /\ forkOwner' = [forkOwner EXCEPT ![SecondFork(i)] = i]

ReleaseBoth(i) ==
  /\ i \in Philosophers
  /\ phase[i] = "Eating"
  /\ forkOwner[FirstFork(i)] = i
  /\ forkOwner[SecondFork(i)] = i
  /\ phase'     = [phase EXCEPT ![i] = "Thinking"]
  /\ forkOwner' = [forkOwner EXCEPT
                     ![FirstFork(i)]  = NoOwner,
                     ![SecondFork(i)] = NoOwner]

Proc(i) == TakeFirst(i) \/ TakeSecond(i) \/ ReleaseBoth(i)

Next == \E i \in Philosophers: Proc(i)

vars == << phase, forkOwner >>

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A i \in Philosophers: SF_vars(Proc(i))

Invariant ==
  \A i \in Philosophers:
    ~(phase[i] = "Eating" /\ phase[(i + 1) % N] = "Eating")

====