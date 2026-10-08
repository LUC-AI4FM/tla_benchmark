------------------------------ MODULE DiningAsym ------------------------------

EXTENDS Naturals, TLC

CONSTANT N

VARIABLES sem, pc

P == 0..(N - 1)
Forks == 0..(N - 1)

Left(i) == i
Right(i) == IF i = 0 THEN N - 1 ELSE i - 1
NextIdx(i) == IF i = N - 1 THEN 0 ELSE i + 1

Lk == {"l1", "l2", "l3", "l4"}
L0 == {"l01", "l02", "l03", "l04"}
AllLabels == Lk \cup L0

TypeOK ==
  /\ sem \in [Forks -> {0, 1}]
  /\ pc \in [P -> AllLabels]

Eating(i) == IF i = 0 THEN pc[i] = "l03" ELSE pc[i] = "l3"

Init ==
  /\ TypeOK
  /\ sem = [f \in Forks |-> 1]
  /\ pc = [i \in P |-> IF i = 0 THEN "l01" ELSE "l1"]

PkAcquireRight(i) ==
  /\ i \in 1..(N - 1)
  /\ pc[i] = "l1"
  /\ sem[Right(i)] = 1
  /\ sem' = [sem EXCEPT ![Right(i)] = 0]
  /\ pc' = [pc EXCEPT ![i] = "l2"]

PkAcquireLeft(i) ==
  /\ i \in 1..(N - 1)
  /\ pc[i] = "l2"
  /\ sem[Left(i)] = 1
  /\ sem' = [sem EXCEPT ![Left(i)] = 0]
  /\ pc' = [pc EXCEPT ![i] = "l3"]

PkEatToRelease(i) ==
  /\ i \in 1..(N - 1)
  /\ pc[i] = "l3"
  /\ sem' = sem
  /\ pc' = [pc EXCEPT ![i] = "l4"]

PkReleaseBoth(i) ==
  /\ i \in 1..(N - 1)
  /\ pc[i] = "l4"
  /\ sem' = [sem EXCEPT ![Right(i)] = 1, ![Left(i)] = 1]
  /\ pc' = [pc EXCEPT ![i] = "l1"]

Pk(i) == PkAcquireRight(i) \/ PkAcquireLeft(i) \/ PkEatToRelease(i) \/ PkReleaseBoth(i)

P0AcquireLeft ==
  /\ pc[0] = "l01"
  /\ sem[Left(0)] = 1
  /\ sem' = [sem EXCEPT ![Left(0)] = 0]
  /\ pc' = [pc EXCEPT ![0] = "l02"]

P0AcquireRight ==
  /\ pc[0] = "l02"
  /\ sem[Right(0)] = 1
  /\ sem' = [sem EXCEPT ![Right(0)] = 0]
  /\ pc' = [pc EXCEPT ![0] = "l03"]

P0EatToRelease ==
  /\ pc[0] = "l03"
  /\ sem' = sem
  /\ pc' = [pc EXCEPT ![0] = "l04"]

P0ReleaseBoth ==
  /\ pc[0] = "l04"
  /\ sem' = [sem EXCEPT ![Left(0)] = 1, ![Right(0)] = 1]
  /\ pc' = [pc EXCEPT ![0] = "l01"]

P0 == P0AcquireLeft \/ P0AcquireRight \/ P0EatToRelease \/ P0ReleaseBoth

Proc(i) == IF i = 0 THEN P0 ELSE Pk(i)

Next == \E i \in P: Proc(i)

Fairness == \A i \in P: SF_<<sem, pc>>(Proc(i))

Spec == Init /\ [][Next]_<<sem, pc>> /\ Fairness

Invariant == \A i \in P: ~(Eating(i) /\ Eating(NextIdx(i)))

StarvationFree == \A i \in P: []<>(Eating(i))

==============================