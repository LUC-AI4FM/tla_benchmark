----------------------------- MODULE DiningPhilosophers -----------------------------

EXTENDS Naturals, Integers

CONSTANT N

ASSUME N \in Nat /\ N >= 2

VARIABLES pc, forks

vars == << pc, forks >>

P == 0 .. (N - 1)

RightFork(i) == i
LeftFork(i)  == (i + N - 1) % N

FirstFork(i)  == IF i = 0 THEN LeftFork(i) ELSE RightFork(i)
SecondFork(i) == IF i = 0 THEN RightFork(i) ELSE LeftFork(i)

Init ==
  /\ pc \in [P -> {"think", "getFirst", "getSecond", "eat", "putFirst", "putSecond"}]
  /\ pc = [i \in P |-> "think"]
  /\ forks \in [P -> {0, 1}]
  /\ forks = [j \in P |-> 1]

Think(i) ==
  /\ i \in P
  /\ pc[i] = "think"
  /\ pc' = [pc EXCEPT ![i] = "getFirst"]
  /\ UNCHANGED forks

GetFirst(i) ==
  /\ i \in P
  /\ pc[i] = "getFirst"
  /\ LET f == FirstFork(i) IN
       /\ forks[f] = 1
       /\ forks' = [forks EXCEPT ![f] = 0]
       /\ pc' = [pc EXCEPT ![i] = "getSecond"]

GetSecond(i) ==
  /\ i \in P
  /\ pc[i] = "getSecond"
  /\ LET s == SecondFork(i) IN
       /\ forks[s] = 1
       /\ forks' = [forks EXCEPT ![s] = 0]
       /\ pc' = [pc EXCEPT ![i] = "eat"]

PutSecond(i) ==
  /\ i \in P
  /\ pc[i] = "eat"
  /\ LET s == SecondFork(i) IN
       /\ forks' = [forks EXCEPT ![s] = 1]
       /\ pc' = [pc EXCEPT ![i] = "putFirst"]

PutFirst(i) ==
  /\ i \in P
  /\ pc[i] = "putFirst"
  /\ LET f == FirstFork(i) IN
       /\ forks' = [forks EXCEPT ![f] = 1]
       /\ pc' = [pc EXCEPT ![i] = "think"]

Phil(i) == Think(i) \/ GetFirst(i) \/ GetSecond(i) \/ PutSecond(i) \/ PutFirst(i)

Next == \E i \in P: Phil(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A i \in P: SF_vars(Phil(i))

MutualExclusion ==
  \A i \in P:
    pc[i] = "eat" =>
      /\ pc[(i + 1) % N] # "eat"
      /\ pc[(i + N - 1) % N] # "eat"

StarvationFreedom ==
  \A i \in P: []<>(pc[i] = "eat")

=============================================================================