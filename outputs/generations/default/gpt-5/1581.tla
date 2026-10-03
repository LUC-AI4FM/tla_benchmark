------------------------------ MODULE DiningPhilosophers ------------------------------

EXTENDS Naturals, Integers

CONSTANT N

ASSUME N \in Nat /\ N >= 2

VARIABLES pc, sem

P == 0..(N - 1)

RightFork(i) == i
LeftFork(i)  == (i - 1) % N

vars == << pc, sem >>

TypeOK ==
  /\ pc \in [P -> {"think", "gotR", "gotL", "eat"}]
  /\ sem \in [P -> BOOLEAN]

Init ==
  /\ pc  = [i \in P |-> "think"]
  /\ sem = [f \in P |-> TRUE]

TakeLeft0(i) ==
  /\ pc[i] = "think"
  /\ sem[LeftFork(i)] = TRUE
  /\ pc'  = [pc EXCEPT ![i] = "gotL"]
  /\ sem' = [sem EXCEPT ![LeftFork(i)] = FALSE]

TakeRight0(i) ==
  /\ pc[i] = "gotL"
  /\ sem[RightFork(i)] = TRUE
  /\ pc'  = [pc EXCEPT ![i] = "eat"]
  /\ sem' = [sem EXCEPT ![RightFork(i)] = FALSE]

TakeRightI(i) ==
  /\ pc[i] = "think"
  /\ sem[RightFork(i)] = TRUE
  /\ pc'  = [pc EXCEPT ![i] = "gotR"]
  /\ sem' = [sem EXCEPT ![RightFork(i)] = FALSE]

TakeLeftI(i) ==
  /\ pc[i] = "gotR"
  /\ sem[LeftFork(i)] = TRUE
  /\ pc'  = [pc EXCEPT ![i] = "eat"]
  /\ sem' = [sem EXCEPT ![LeftFork(i)] = FALSE]

PutDown(i) ==
  /\ pc[i] = "eat"
  /\ pc'  = [pc EXCEPT ![i] = "think"]
  /\ sem' = [sem EXCEPT
               ![LeftFork(i)]  = TRUE,
               ![RightFork(i)] = TRUE]

Proc(i) ==
  \/ /\ i = 0 /\ TakeLeft0(i)
  \/ /\ i = 0 /\ TakeRight0(i)
  \/ /\ i # 0 /\ TakeRightI(i)
  \/ /\ i # 0 /\ TakeLeftI(i)
  \/ PutDown(i)

Next == \E i \in P: Proc(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A i \in P: SF_vars(Proc(i))

SafetyInvariant ==
  \A i \in P:
    ~(/\ pc[i] = "eat" /\ pc[(i + 1) % N] = "eat")

StarvationFreedom ==
  \A i \in P: []<>(pc[i] = "eat")

=================================