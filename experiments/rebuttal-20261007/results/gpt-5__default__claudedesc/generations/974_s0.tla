----------------------------- MODULE RegularRegisters -----------------------------
EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat \ {0}

Proc == 0..(N-1)

VARIABLES pc, x, y

vars == << pc, x, y >>

Prev(i) == IF i = 0 THEN N-1 ELSE i-1

TypeOK ==
  /\ pc \in [Proc -> {"a1", "a2", "b", "Done"}]
  /\ x \in [Proc -> SUBSET {0,1}]
  /\ \A i \in Proc: x[i] # {}
  /\ y \in [Proc -> {0,1}]

Init ==
  /\ pc = [i \in Proc |-> "a1"]
  /\ x  = [i \in Proc |-> {0}]
  /\ y \in [Proc -> {0,1}]

A1(i) ==
  /\ i \in Proc
  /\ pc[i] = "a1"
  /\ x'  = [x EXCEPT ![i] = {0,1}]
  /\ pc' = [pc EXCEPT ![i] = "a2"]
  /\ y'  = y

A2(i) ==
  /\ i \in Proc
  /\ pc[i] = "a2"
  /\ x'  = [x EXCEPT ![i] = {1}]
  /\ pc' = [pc EXCEPT ![i] = "b"]
  /\ y'  = y

B(i) ==
  /\ i \in Proc
  /\ pc[i] = "b"
  /\ \E v \in x[Prev(i)]: y' = [y EXCEPT ![i] = v]
  /\ pc' = [pc EXCEPT ![i] = "Done"]
  /\ x'  = x

Next ==
  \E i \in Proc: A1(i) \/ A2(i) \/ B(i)

Spec ==
  Init /\ [][Next]_vars

PCorrect ==
  (\A i \in Proc: pc[i] = "Done") => (\E i \in Proc: y[i] = 1)

WritesDone ==
  \A i \in Proc: (pc[i] \in {"b","Done"}) => x[i] = {1}

ProgressOrRead1 ==
  (\E i \in Proc: pc[i] # "Done") \/ (\E i \in Proc: y[i] = 1)

Inv ==
  TypeOK /\ WritesDone /\ ProgressOrRead1

Termination ==
  \A i \in Proc: <> (pc[i] = "Done")

THEOREM InvIsInductive ==
  Init /\ [][Next]_vars => []Inv

THEOREM InvImpliesPCorrect ==
  []Inv => []PCorrect

THEOREM Correctness ==
  Spec => []PCorrect

THEOREM Correctness2 ==
  (Init /\ [][Next]_vars => []Inv) /\ ([]Inv => []PCorrect)
=============================================================================