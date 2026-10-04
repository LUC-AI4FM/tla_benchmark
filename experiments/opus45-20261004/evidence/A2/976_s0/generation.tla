---------------------------- MODULE SimpleCircle ----------------------------
EXTENDS Integers, Sequences, TLAPS

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

VARIABLES x, y, pc

vars == <<x, y, pc>>

Procs == 0..(N-1)

Init ==
    /\ x = [i \in Procs |-> 0]
    /\ y = [i \in Procs |-> 0]
    /\ pc = [i \in Procs |-> "a"]

a(self) ==
    /\ pc[self] = "a"
    /\ x' = [x EXCEPT ![self] = 1]
    /\ pc' = [pc EXCEPT ![self] = "b"]
    /\ y' = y

b(self) ==
    /\ pc[self] = "b"
    /\ y' = [y EXCEPT ![self] = x[(self - 1) % N]]
    /\ pc' = [pc EXCEPT ![self] = "Done"]
    /\ x' = x

proc(self) == a(self) \/ b(self)

Next == \E self \in Procs : proc(self)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeOK ==
    /\ x \in [Procs -> {0, 1}]
    /\ y \in [Procs -> {0, 1}]
    /\ pc \in [Procs -> {"a", "b", "Done"}]

AllDone == \A i \in Procs : pc[i] = "Done"

PCorrect == AllDone => \E i \in Procs : y[i] = 1

PastA(i) == pc[i] \in {"b", "Done"}

SomeNotDone == \E i \in Procs : pc[i] # "Done"

SomeYOne == \E i \in Procs : y[i] = 1

Inv ==
    /\ TypeOK
    /\ \A i \in Procs : PastA(i) => x[i] = 1
    /\ SomeNotDone \/ SomeYOne

THEOREM InitInv == Init => Inv
<1>1. Init => TypeOK
  BY NAssumption DEF Init, TypeOK, Procs
<1>2. Init => (\A i \in Procs : PastA(i) => x[i] = 1)
  BY DEF Init, PastA, Procs
<1>3. Init => (SomeNotDone \/ SomeYOne)
  BY NAssumption DEF Init, SomeNotDone, Procs
<1>. QED BY <1>1, <1>2, <1>3 DEF Inv

THEOREM NextInv == Inv /\ Next => Inv'
<1>. SUFFICES ASSUME Inv, Next PROVE Inv' OBVIOUS
<1>1. TypeOK'
  BY DEF Inv, TypeOK, Next, proc, a, b, Procs
<1>2. \A i \in Procs : PastA(i)' => x'[i] = 1
  BY DEF Inv, TypeOK, Next, proc, a, b, PastA, Procs
<1>3. SomeNotDone' \/ SomeYOne'
  <2>1. CASE \E self \in Procs : a(self)
    BY <2>1 DEF Inv, SomeNotDone, SomeYOne, a, Procs
  <2>2. CASE \E self \in Procs : b(self)
    <3>. PICK self \in Procs : b(self) BY <2>2
    <3>1. CASE SomeYOne
      BY <3>1 DEF Inv, SomeYOne, b, Procs
    <3>2. CASE ~SomeYOne /\ SomeNotDone
      <4>1. pc[(self - 1) % N] \in {"b", "Done"}
        BY <3>2, NAssumption DEF Inv, SomeNotDone, b, Procs
      <4>2. x[(self - 1) % N] = 1
        BY <4>1, NAssumption DEF Inv, PastA, Procs
      <4>3. y'[self] = 1
        BY <4>2 DEF b, Procs
      <4>. QED BY <4>3 DEF SomeYOne, Procs
    <3>. QED BY <3>1, <3>2 DEF Inv
  <2>. QED BY <2>1, <2>2 DEF Next, proc
<1>. QED BY <1>1, <1>2, <1>3 DEF Inv

THEOREM InvImpliesPCorrect == Inv => PCorrect
BY DEF Inv, PCorrect, AllDone, SomeNotDone, SomeYOne, Procs

THEOREM Correctness == Spec => []PCorrect
<1>1. Init => Inv
  BY InitInv
<1>2. Inv /\ [Next]_vars => Inv'
  <2>1. Inv /\ Next => Inv'
    BY NextInv
  <2>2. Inv /\ UNCHANGED vars => Inv'
    BY DEF Inv, TypeOK, PastA, SomeNotDone, SomeYOne, vars
  <2>. QED BY <2>1, <2>2
<1>3. Inv => PCorrect
  BY InvImpliesPCorrect
<1>. QED BY <1>1, <1>2, <1>3, PTL DEF Spec

THEOREM Correctness2 == Spec => []PCorrect
BY InitInv, NextInv, InvImpliesPCorrect, PTL DEF Spec, vars

=============================================================================