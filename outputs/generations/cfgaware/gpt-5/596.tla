------------------------------ MODULE OneVarWF ------------------------------

EXTENDS Naturals, TLC, Sequences

VARIABLES x

Init ==
  x = 0

Next ==
  \/ /\ x = 0
     /\ x' \in {1, 2}
  \/ /\ x # 0
     /\ x' = 0

Spec ==
  Init /\ [][Next]_x /\ WF_x(Next)

EventuallyStabilizeNot1 ==
  <>[] (x # 1)

EventuallyStabilizeNot2 ==
  <>[] (x # 2)

RepeatedZero ==
  []<>(x = 0)

NotEventuallyStabilizeNot1 ==
  ~EventuallyStabilizeNot1

State ==
  [x : {0, 1, 2}]

StateOK(s) ==
  s \in State

StepOK(s, t) ==
  /\ StateOK(s)
  /\ StateOK(t)
  /\ \/ /\ s.x = 0 /\ t.x \in {1, 2}
     \/ /\ s.x # 0 /\ t.x = 0

SequenceOK(seq) ==
  /\ seq \in Seq(State)
  /\ IF Len(seq) <= 1
     THEN TRUE
     ELSE \A i \in 1..(Len(seq) - 1): StepOK(seq[i], seq[i + 1])

CounterexampleTrace ==
  << [x |-> 0], [x |-> 1], [x |-> 0], [x |-> 2], [x |-> 0] >>

PostCondition ==
  /\ SequenceOK(CounterexampleTrace)
  /\ Head(CounterexampleTrace) = [x |-> 0]
  /\ Tail(CounterexampleTrace)[1] \in { [x |-> 1], [x |-> 2] }

==============================