----------------------------- MODULE DiningPhilosophers -----------------------------
EXTENDS Naturals, Integers

CONSTANT N

ASSUME N \in Nat /\ N >= 2

VARIABLES fork, stage

I == 0..(N-1)

Left(i) == i
Right(i) == (i + N - 1) \mod N

FirstFork(i) == IF i = 0 THEN Left(i) ELSE Right(i)
SecondFork(i) == IF i = 0 THEN Right(i) ELSE Left(i)

HasLeft(i) == fork[Left(i)] = i
HasRight(i) == fork[Right(i)] = i
Eating(i) == HasLeft(i) /\ HasRight(i)

Init ==
  /\ stage = [i \in I |-> "Think"]
  /\ fork  = [j \in I |-> -1]

Proc(i) ==
  \/ /\ stage[i] = "Think"
     /\ stage' = [stage EXCEPT ![i] = "TakeFirst"]
     /\ UNCHANGED fork
  \/ /\ stage[i] = "TakeFirst"
     /\ fork[FirstFork(i)] = -1
     /\ stage' = [stage EXCEPT ![i] = "TakeSecond"]
     /\ fork'  = [fork EXCEPT ![FirstFork(i)] = i]
  \/ /\ stage[i] = "TakeSecond"
     /\ fork[FirstFork(i)] = i
     /\ fork[SecondFork(i)] = -1
     /\ stage' = [stage EXCEPT ![i] = "Eat"]
     /\ fork'  = [fork EXCEPT ![SecondFork(i)] = i]
  \/ /\ stage[i] = "Eat"
     /\ fork[FirstFork(i)] = i
     /\ fork[SecondFork(i)] = i
     /\ stage' = [stage EXCEPT ![i] = "Think"]
     /\ fork'  = [fork EXCEPT ![FirstFork(i)] = -1,
                          ![SecondFork(i)] = -1]

Next == \E i \in I: Proc(i)

vars == << fork, stage >>

Spec == Init /\ [][Next]_vars /\ \A i \in I: SF_vars(Proc(i))

Invariant ==
  \A i \in I:
    ~ (Eating(i) /\ Eating(((i + 1) \mod N)))

StarvationFree == \A i \in I: []<>(Eating(i))
=============================================================================