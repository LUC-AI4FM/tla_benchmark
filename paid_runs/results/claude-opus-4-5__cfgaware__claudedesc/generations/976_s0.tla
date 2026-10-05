---------------------------- MODULE SimpleProgram ----------------------------
EXTENDS Integers, TLAPS

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

VARIABLES x, y, pc

vars == <<x, y, pc>>

Procs == 0..(N-1)

Init == /\ x = [i \in Procs |-> 0]
        /\ y = [i \in Procs |-> 0]
        /\ pc = [i \in Procs |-> "a"]

a(self) == /\ pc[self] = "a"
           /\ x' = [x EXCEPT ![self] = 1]
           /\ pc' = [pc EXCEPT ![self] = "b"]
           /\ y' = y

b(self) == /\ pc[self] = "b"
           /\ y' = [y EXCEPT ![self] = x[(self - 1) % N]]
           /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ x' = x

Proc(self) == a(self) \/ b(self)

Terminating == /\ \A self \in Procs: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Procs: Proc(self)) \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeOK == /\ x \in [Procs -> {0, 1}]
          /\ y \in [Procs -> {0, 1}]
          /\ pc \in [Procs -> {"a", "b", "Done"}]

PCorrect == (\A i \in Procs: pc[i] = "Done") => (\E i \in Procs: y[i] = 1)

Inv == /\ TypeOK
       /\ \A i \in Procs: pc[i] \in {"b", "Done"} => x[i] = 1
       /\ (\E i \in Procs: pc[i] # "Done") \/ (\E i \in Procs: y[i] = 1)

THEOREM Correctness == Spec => []PCorrect
<1>1. Init => Inv
  <2>1. Init => TypeOK
    BY NAssumption DEF Init, TypeOK, Procs
  <2>2. Init => (\A i \in Procs: pc[i] \in {"b", "Done"} => x[i] = 1)
    BY DEF Init, Procs
  <2>3. Init => ((\E i \in Procs: pc[i] # "Done") \/ (\E i \in Procs: y[i] = 1))
    BY NAssumption DEF Init, Procs
  <2>. QED
    BY <2>1, <2>2, <2>3 DEF Inv
<1>2. Inv /\ [Next]_vars => Inv'
  <2>1. SUFFICES ASSUME Inv, [Next]_vars
                 PROVE Inv'
    OBVIOUS
  <2>2. CASE \E self \in Procs: a(self)
    <3>1. PICK self \in Procs: a(self)
      BY <2>2
    <3>2. TypeOK'
      BY <3>1, NAssumption DEF Inv, TypeOK, a, Procs
    <3>3. \A i \in Procs: pc'[i] \in {"b", "Done"} => x'[i] = 1
      BY <3>1 DEF Inv, TypeOK, a, Procs
    <3>4. (\E i \in Procs: pc'[i] # "Done") \/ (\E i \in Procs: y'[i] = 1)
      BY <3>1 DEF Inv, TypeOK, a, Procs
    <3>. QED
      BY <3>2, <3>3, <3>4 DEF Inv
  <2>3. CASE \E self \in Procs: b(self)
    <3>1. PICK self \in Procs: b(self)
      BY <2>3
    <3>2. TypeOK'
      BY <3>1, NAssumption DEF Inv, TypeOK, b, Procs
    <3>3. \A i \in Procs: pc'[i] \in {"b", "Done"} => x'[i] = 1
      BY <3>1 DEF Inv, TypeOK, b, Procs
    <3>4. (\E i \in Procs: pc'[i] # "Done") \/ (\E i \in Procs: y'[i] = 1)
      <4>1. CASE \A i \in Procs: pc'[i] = "Done"
        <5>1. \A i \in Procs: pc[i] \in {"b", "Done"}
          BY <3>1, <4>1 DEF Inv, TypeOK, b, Procs
        <5>2. \A i \in Procs: x[i] = 1
          BY <5>1 DEF Inv
        <5>3. x[(self - 1) % N] = 1
          BY <5>2, NAssumption DEF Procs
        <5>4. y'[self] = 1
          BY <3>1, <5>3 DEF b
        <5>. QED
          BY <5>4 DEF Procs
      <4>2. CASE \E i \in Procs: pc'[i] # "Done"
        BY <4>2
      <4>. QED
        BY <4>1, <4>2
    <3>. QED
      BY <3>2, <3>3, <3>4 DEF Inv
  <2>4. CASE Terminating
    BY <2>4 DEF Inv, TypeOK, Terminating, vars
  <2>5. CASE UNCHANGED vars
    BY <2>5 DEF Inv, TypeOK, vars
  <2>. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
<1>3. Inv => PCorrect
  BY DEF Inv, PCorrect
<1>. QED
  BY <1>1, <1>2, <1>3, PTL DEF Spec

THEOREM Correctness2 == Spec => []PCorrect
<1>1. Init => Inv
  BY NAssumption DEF Init, Inv, TypeOK, Procs
<1>2. Inv /\ [Next]_vars => Inv'
  BY NAssumption DEF Inv, TypeOK, Next, a, b, Terminating, vars, Procs
<1>3. Inv => PCorrect
  BY DEF Inv, PCorrect
<1>. QED
  BY <1>1, <1>2, <1>3, PTL DEF Spec

=============================================================================