------------------------------ MODULE DiningPhilosophers ------------------------------

EXTENDS Naturals, Integers

CONSTANT N

ASSUME N \in Nat /\ N >= 2

VARIABLES sem, pc

Phil == 0..(N - 1)
Fork == Phil

Succ(i) == IF i = N - 1 THEN 0 ELSE i + 1

LeftFork(i) == i
RightFork(i) == Succ(i)

Vars == << sem, pc >>

Init ==
  /\ sem = [ f \in Fork |-> 1 ]
  /\ pc  = [ i \in Phil |-> "think" ]

Think(i) ==
  /\ i \in Phil
  /\ pc[i] = "think"
  /\ pc' = [pc EXCEPT ![i] = IF i = 0 THEN "tryL0" ELSE "tryR"]
  /\ UNCHANGED sem

TryR(i) ==
  /\ i \in Phil
  /\ i # 0
  /\ pc[i] = "tryR"
  /\ sem[RightFork(i)] = 1
  /\ sem' = [sem EXCEPT ![RightFork(i)] = 0]
  /\ pc'  = [pc  EXCEPT ![i] = "tryL"]

TryL(i) ==
  /\ i \in Phil
  /\ i # 0
  /\ pc[i] = "tryL"
  /\ sem[LeftFork(i)] = 1
  /\ sem' = [sem EXCEPT ![LeftFork(i)] = 0]
  /\ pc'  = [pc  EXCEPT ![i] = "eat"]

Eat(i) ==
  /\ i \in Phil
  /\ pc[i] = "eat"
  /\ pc' = [pc EXCEPT ![i] = IF i = 0 THEN "putR0" ELSE "putL"]
  /\ UNCHANGED sem

PutL(i) ==
  /\ i \in Phil
  /\ i # 0
  /\ pc[i] = "putL"
  /\ sem' = [sem EXCEPT ![LeftFork(i)] = 1]
  /\ pc'  = [pc  EXCEPT ![i] = "putR"]

PutR(i) ==
  /\ i \in Phil
  /\ i # 0
  /\ pc[i] = "putR"
  /\ sem' = [sem EXCEPT ![RightFork(i)] = 1]
  /\ pc'  = [pc  EXCEPT ![i] = "think"]

TryL0(i) ==
  /\ i \in Phil
  /\ i = 0
  /\ pc[i] = "tryL0"
  /\ sem[LeftFork(i)] = 1
  /\ sem' = [sem EXCEPT ![LeftFork(i)] = 0]
  /\ pc'  = [pc  EXCEPT ![i] = "tryR0"]

TryR0(i) ==
  /\ i \in Phil
  /\ i = 0
  /\ pc[i] = "tryR0"
  /\ sem[RightFork(i)] = 1
  /\ sem' = [sem EXCEPT ![RightFork(i)] = 0]
  /\ pc'  = [pc  EXCEPT ![i] = "eat"]

PutR0(i) ==
  /\ i \in Phil
  /\ i = 0
  /\ pc[i] = "putR0"
  /\ sem' = [sem EXCEPT ![RightFork(i)] = 1]
  /\ pc'  = [pc  EXCEPT ![i] = "putL0"]

PutL0(i) ==
  /\ i \in Phil
  /\ i = 0
  /\ pc[i] = "putL0"
  /\ sem' = [sem EXCEPT ![LeftFork(i)] = 1]
  /\ pc'  = [pc  EXCEPT ![i] = "think"]

Proc(i) ==
  Think(i)
  \/ TryR(i) \/ TryL(i)
  \/ Eat(i)
  \/ PutL(i) \/ PutR(i)
  \/ TryL0(i) \/ TryR0(i)
  \/ PutR0(i) \/ PutL0(i)

Next == \E i \in Phil: Proc(i)

Spec == Init /\ [][Next]_Vars /\ \A i \in Phil: SF_Vars(Proc(i))

Eating(i) == pc[i] = "eat"

NoAdjacentEating == \A i \in Phil: ~(Eating(i) /\ Eating(Succ(i)))

StarvationFreedom == \A i \in Phil: []<>(Eating(i))

=============================================================================