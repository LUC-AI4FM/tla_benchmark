------------------------------ MODULE DiningPhilosophers ------------------------------

EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat /\ N >= 2

VARIABLES pc, sem

P == 0..(N - 1)
F == P

NextId(i) == IF i = N - 1 THEN 0 ELSE i + 1
PrevId(i) == IF i = 0 THEN N - 1 ELSE i - 1

RightFork(i) == i
LeftFork(i) == PrevId(i)

FirstFork(i) == IF i = 0 THEN LeftFork(i) ELSE RightFork(i)
SecondFork(i) == IF i = 0 THEN RightFork(i) ELSE LeftFork(i)

vars == << pc, sem >>

Init ==
  /\ pc = [i \in P |-> "think"]
  /\ sem = [f \in F |-> 1]

ThinkStep(i) ==
  /\ i \in P
  /\ pc[i] = "think"
  /\ pc' = [pc EXCEPT ![i] = "get1"]
  /\ UNCHANGED sem

TakeFirst(i) ==
  /\ i \in P
  /\ pc[i] = "get1"
  /\ sem[FirstFork(i)] = 1
  /\ pc' = [pc EXCEPT ![i] = "get2"]
  /\ sem' = [sem EXCEPT ![FirstFork(i)] = 0]

TakeSecond(i) ==
  /\ i \in P
  /\ pc[i] = "get2"
  /\ sem[SecondFork(i)] = 1
  /\ pc' = [pc EXCEPT ![i] = "eat"]
  /\ sem' = [sem EXCEPT ![SecondFork(i)] = 0]

FinishEat(i) ==
  /\ i \in P
  /\ pc[i] = "eat"
  /\ pc' = [pc EXCEPT ![i] = "put1"]
  /\ sem' = [sem EXCEPT ![SecondFork(i)] = 1]

PutFirst(i) ==
  /\ i \in P
  /\ pc[i] = "put1"
  /\ pc' = [pc EXCEPT ![i] = "put2"]
  /\ sem' = [sem EXCEPT ![FirstFork(i)] = 1]

DonePut(i) ==
  /\ i \in P
  /\ pc[i] = "put2"
  /\ pc' = [pc EXCEPT ![i] = "think"]
  /\ UNCHANGED sem

Proc(i) ==
  ThinkStep(i)
  \/ TakeFirst(i)
  \/ TakeSecond(i)
  \/ FinishEat(i)
  \/ PutFirst(i)
  \/ DonePut(i)

Next ==
  \E i \in P : Proc(i)

Eating(i) == pc[i] = "eat"

MutualExclusion ==
  \A i \in P : ~(Eating(i) /\ Eating(NextId(i)))

TypeInv ==
  /\ pc \in [P -> {"think", "get1", "get2", "eat", "put1", "put2"}]
  /\ sem \in [F -> {0, 1}]

SafetyInv == TypeInv /\ MutualExclusion

StarvationFreedom ==
  \A i \in P : []<>Eating(i)

Spec ==
  Init
  /\ [][Next]_vars
  /\ \A i \in P : SF_vars(Proc(i))

=============================================================================