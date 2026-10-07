----------------------------- MODULE DiningPhilosophers -----------------------------

EXTENDS Naturals

CONSTANT N

VARIABLES sem, pc

P == 0..(N - 1)

Right(i) == i
Left(i)  == IF i = 0 THEN N - 1 ELSE i - 1

F1(i) == IF i = 0 THEN Left(i) ELSE Right(i)
F2(i) == IF i = 0 THEN Right(i) ELSE Left(i)

vars == << sem, pc >>

Init ==
  /\ N \in Nat /\ N >= 1
  /\ sem \in [P -> {0, 1}]
  /\ sem = [i \in P |-> 1]
  /\ pc \in [P -> {"Want1", "Want2", "Eat", "Rel2"}]
  /\ pc = [i \in P |-> "Want1"]

Try1(i) ==
  /\ i \in P
  /\ pc[i] = "Want1"
  /\ sem[F1(i)] = 1
  /\ sem' = [sem EXCEPT ![F1(i)] = 0]
  /\ pc' = [pc EXCEPT ![i] = "Want2"]

Try2(i) ==
  /\ i \in P
  /\ pc[i] = "Want2"
  /\ sem[F2(i)] = 1
  /\ sem' = [sem EXCEPT ![F2(i)] = 0]
  /\ pc' = [pc EXCEPT ![i] = "Eat"]

Rel1(i) ==
  /\ i \in P
  /\ pc[i] = "Eat"
  /\ sem[F1(i)] = 0
  /\ sem' = [sem EXCEPT ![F1(i)] = 1]
  /\ pc' = [pc EXCEPT ![i] = "Rel2"]

Rel2(i) ==
  /\ i \in P
  /\ pc[i] = "Rel2"
  /\ sem[F2(i)] = 0
  /\ sem' = [sem EXCEPT ![F2(i)] = 1]
  /\ pc' = [pc EXCEPT ![i] = "Want1"]

Phil(i) == Try1(i) \/ Try2(i) \/ Rel1(i) \/ Rel2(i)

Next == \E i \in P : Phil(i)

Spec == Init /\ [][Next]_vars /\ \A i \in P : SF_vars(Phil(i))

NextIdx(i) == IF i = N - 1 THEN 0 ELSE i + 1

Invariant ==
  \A i \in P : ~(pc[i] = "Eat" /\ pc[NextIdx(i)] = "Eat")

StarvationFree ==
  \A i \in P : []<>(pc[i] = "Eat")

=============================================================================