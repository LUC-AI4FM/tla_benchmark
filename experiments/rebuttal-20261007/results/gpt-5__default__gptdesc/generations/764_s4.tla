------------------------------ MODULE DiningPhilosophers ------------------------------

EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat /\ N >= 2

Proc == 0..(N-1)
Fork == 0..(N-1)

NextIdx(i) == IF i = N-1 THEN 0 ELSE i+1
PrevIdx(i) == IF i = 0 THEN N-1 ELSE i-1

LeftFork(i)  == i
RightFork(i) == PrevIdx(i)

Labels == {"think", "getL", "getR", "eat"}

FirstFork(i)  == IF i = 0 THEN LeftFork(i)  ELSE RightFork(i)
SecondFork(i) == IF i = 0 THEN RightFork(i) ELSE LeftFork(i)

FirstLabel(i)  == IF i = 0 THEN "getL" ELSE "getR"
SecondLabel(i) == IF i = 0 THEN "getR" ELSE "getL"

VARIABLES pc, sem

vars == << pc, sem >>

Init ==
  /\ pc  = [i \in Proc |-> "think"]
  /\ sem = [f \in Fork |-> TRUE]

StepStart(i) ==
  /\ i \in Proc
  /\ pc[i] = "think"
  /\ pc' = [pc EXCEPT ![i] = FirstLabel(i)]
  /\ UNCHANGED sem

StepGetL(i) ==
  /\ i \in Proc
  /\ pc[i] = "getL"
  /\ sem[LeftFork(i)] = TRUE
  /\ pc'  = [pc EXCEPT ![i] = IF i = 0 THEN "getR" ELSE "eat"]
  /\ sem' = [sem EXCEPT ![LeftFork(i)] = FALSE]

StepGetR(i) ==
  /\ i \in Proc
  /\ pc[i] = "getR"
  /\ sem[RightFork(i)] = TRUE
  /\ pc'  = [pc EXCEPT ![i] = IF i = 0 THEN "eat" ELSE "getL"]
  /\ sem' = [sem EXCEPT ![RightFork(i)] = FALSE]

StepEat(i) ==
  /\ i \in Proc
  /\ pc[i] = "eat"
  /\ pc'  = [pc EXCEPT ![i] = "think"]
  /\ sem' = [sem EXCEPT ![LeftFork(i)] = TRUE,
                      ![RightFork(i)] = TRUE]

Proc(i) == StepStart(i) \/ StepGetL(i) \/ StepGetR(i) \/ StepEat(i)

Next == \E i \in Proc: Proc(i)

Spec == Init /\ [][Next]_vars /\ (\A i \in Proc: SF_vars(Proc(i)))

TypeInvariant ==
  /\ pc \in [Proc -> Labels]
  /\ sem \in [Fork -> BOOLEAN]

Eating(i) == pc[i] = "eat"

AdjacentNeverBothEat ==
  \A i \in Proc: ~(Eating(i) /\ Eating(NextIdx(i)))

StarvationFreedom ==
  \A i \in Proc: []<>(Eating(i))

=============================================================================