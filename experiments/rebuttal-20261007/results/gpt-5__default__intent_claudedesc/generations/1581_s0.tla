----------------------------- MODULE DiningPhilosophers -----------------------------

EXTENDS Naturals

CONSTANTS N, Special

ASSUME N \in Nat \* number of philosophers
  /\ N >= 2
  /\ Special \in 0..(N - 1) \* the unique philosopher who picks up left first

P == 0..(N - 1)
Forks == P

NextIdx(i) == IF i = N - 1 THEN 0 ELSE i + 1
PrevIdx(i) == IF i = 0 THEN N - 1 ELSE i - 1

LeftFork(i) == i
RightFork(i) == PrevIdx(i)

FirstFork(i) == IF i = Special THEN LeftFork(i) ELSE RightFork(i)
SecondFork(i) == IF i = Special THEN RightFork(i) ELSE LeftFork(i)

None == "None"
States == {"WantFirst", "WantSecond", "Eating"}

VARIABLES owner, stage

vars == << owner, stage >>

TypeOK ==
  /\ owner \in [Forks -> (P \cup {None})]
  /\ stage \in [P -> States]

Init ==
  /\ TypeOK
  /\ \A f \in Forks: owner[f] = None
  /\ \A i \in P: stage[i] = "WantFirst"

TryFirst(i) ==
  /\ i \in P
  /\ stage[i] = "WantFirst"
  /\ owner[FirstFork(i)] = None
  /\ owner' = [owner EXCEPT ![FirstFork(i)] = i]
  /\ stage' = [stage EXCEPT ![i] = "WantSecond"]

TrySecond(i) ==
  /\ i \in P
  /\ stage[i] = "WantSecond"
  /\ owner[FirstFork(i)] = i
  /\ owner[SecondFork(i)] = None
  /\ owner' = [owner EXCEPT ![SecondFork(i)] = i]
  /\ stage' = [stage EXCEPT ![i] = "Eating"]

Release(i) ==
  /\ i \in P
  /\ stage[i] = "Eating"
  /\ owner[FirstFork(i)] = i
  /\ owner[SecondFork(i)] = i
  /\ owner' = [owner EXCEPT ![FirstFork(i)] = None, ![SecondFork(i)] = None]
  /\ stage' = [stage EXCEPT ![i] = "WantFirst"]

Proc(i) == TryFirst(i) \/ TrySecond(i) \/ Release(i)

Next == \E i \in P: Proc(i)

\* Safety: No two adjacent philosophers eat simultaneously.
AdjacentSafe ==
  \A i \in P:
    ~(stage[i] = "Eating" /\ stage[NextIdx(i)] = "Eating")

\* Liveness: Every philosopher eats infinitely often (starvation freedom).
StarvationFreedom ==
  \A i \in P: []<>(stage[i] = "Eating")

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A i \in P: SF_vars(Proc(i))

=============================================================================