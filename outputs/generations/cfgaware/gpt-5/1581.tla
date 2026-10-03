----------------------------- MODULE DiningPhilosophers -----------------------------

EXTENDS Naturals

CONSTANT N

VARIABLES pc, sem

P == 0..(N - 1)

Succ(i) == IF i = N - 1 THEN 0 ELSE i + 1

Left(i) == i
Right(i) == Succ(i)

First(i) == IF i = 0 THEN Left(i) ELSE Right(i)
Second(i) == IF i = 0 THEN Right(i) ELSE Left(i)

Init ==
  /\ pc = [i \in P |-> "think"]
  /\ sem = [k \in P |-> TRUE]

TryFirst(i) ==
  /\ i \in P
  /\ pc[i] = "think"
  /\ sem[First(i)] = TRUE
  /\ pc' = [pc EXCEPT ![i] = "got1"]
  /\ sem' = [sem EXCEPT ![First(i)] = FALSE]

TrySecond(i) ==
  /\ i \in P
  /\ pc[i] = "got1"
  /\ sem[Second(i)] = TRUE
  /\ pc' = [pc EXCEPT ![i] = "eat"]
  /\ sem' = [sem EXCEPT ![Second(i)] = FALSE]

EatStep(i) ==
  /\ i \in P
  /\ pc[i] = "eat"
  /\ pc' = [pc EXCEPT ![i] = "rel1"]
  /\ UNCHANGED sem

Release1(i) ==
  /\ i \in P
  /\ pc[i] = "rel1"
  /\ pc' = [pc EXCEPT ![i] = "rel2"]
  /\ sem' = [sem EXCEPT ![First(i)] = TRUE]

Release2(i) ==
  /\ i \in P
  /\ pc[i] = "rel2"
  /\ pc' = [pc EXCEPT ![i] = "think"]
  /\ sem' = [sem EXCEPT ![Second(i)] = TRUE]

Proc(i) == TryFirst(i) \/ TrySecond(i) \/ EatStep(i) \/ Release1(i) \/ Release2(i)

Next == \E i \in P : Proc(i)

vars == << pc, sem >>

Fairness == \A i \in P : SF_vars(Proc(i))

Spec == Init /\ [][Next]_vars /\ Fairness

Invariant ==
  \A i \in P :
    ~(pc[i] = "eat" /\ pc[Succ(i)] = "eat")

StarvationFree ==
  \A i \in P : []<>(pc[i] = "eat")

=============================================================================