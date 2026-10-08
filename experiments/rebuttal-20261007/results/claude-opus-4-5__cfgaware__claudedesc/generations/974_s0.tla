---------------------------- MODULE SimpleRegular ----------------------------

EXTENDS Naturals, TLAPS, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

VARIABLES x, y, pc

vars == <<x, y, pc>>

Procs == 0..N-1

Labels == {"a1", "a2", "b", "Done"}

TypeOK == /\ x \in [Procs -> SUBSET {0,1}]
          /\ \A i \in Procs : x[i] # {}
          /\ y \in [Procs -> {0,1}]
          /\ pc \in [Procs -> Labels]

Init == /\ x = [i \in Procs |-> {0}]
        /\ y = [i \in Procs |-> 0]
        /\ pc = [i \in Procs |-> "a1"]

a1(self) == /\ pc[self] = "a1"
            /\ x' = [x EXCEPT ![self] = {0,1}]
            /\ pc' = [pc EXCEPT ![self] = "a2"]
            /\ y' = y

a2(self) == /\ pc[self] = "a2"
            /\ x' = [x EXCEPT ![self] = {1}]
            /\ pc' = [pc EXCEPT ![self] = "b"]
            /\ y' = y

b(self) == /\ pc[self] = "b"
           /\ \E v \in x[(self - 1 + N) % N] : y' = [y EXCEPT ![self] = v]
           /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ x' = x

Next == \E self \in Procs : a1(self) \/ a2(self) \/ b(self)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(\A self \in Procs : pc[self] = "Done")

PCorrect == (\A i \in Procs : pc[i] = "Done") => (\E i \in Procs : y[i] = 1)

Inv == /\ TypeOK
       /\ \A i \in Procs : pc[i] \in {"b", "Done"} => x[i] = {1}
       /\ (\E i \in Procs : pc[i] # "Done") \/ (\E i \in Procs : y[i] = 1)

THEOREM Correctness == Spec => []PCorrect
<1>1. Init => Inv
  <2>1. Init => TypeOK
    BY NAssumption DEF Init, TypeOK, Procs
  <2>2. Init => \A i \in Procs : pc[i] \in {"b", "Done"} => x[i] = {1}
    BY DEF Init, Procs
  <2>3. Init => (\E i \in Procs : pc[i] # "Done") \/ (\E i \in Procs : y[i] = 1)
    BY NAssumption DEF Init, Procs
  <2>. QED BY <2>1, <2>2, <2>3 DEF Inv
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv' OBVIOUS
  <2>1. CASE Next
    <3>1. CASE \E self \in Procs : a1(self)
      BY <3>1, NAssumption DEF Inv, TypeOK, a1, Procs, Labels
    <3>2. CASE \E self \in Procs : a2(self)
      BY <3>2, NAssumption DEF Inv, TypeOK, a2, Procs, Labels
    <3>3. CASE \E self \in Procs : b(self)
      BY <3>3, NAssumption DEF Inv, TypeOK, b, Procs, Labels
    <3>. QED BY <2>1, <3>1, <3>2, <3>3 DEF Next
  <2>2. CASE UNCHANGED vars
    BY <2>2 DEF Inv, TypeOK, vars
  <2>. QED BY <2>1, <2>2
<1>3. Inv => PCorrect
  BY DEF Inv, PCorrect, Procs
<1>. QED BY <1>1, <1>2, <1>3, PTL DEF Spec

THEOREM Correctness2 == Spec => []PCorrect
<1>1. Init /\ [][Next]_vars => []Inv
  <2>1. Init => Inv
    BY NAssumption DEF Init, Inv, TypeOK, Procs
  <2>2. Inv /\ [Next]_vars => Inv'
    BY NAssumption DEF Inv, TypeOK, Next, a1, a2, b, Procs, Labels, vars
  <2>. QED BY <2>1, <2>2, PTL
<1>2. []Inv => []PCorrect
  <2>1. Inv => PCorrect
    BY DEF Inv, PCorrect, Procs
  <2>. QED BY <2>1, PTL
<1>. QED BY <1>1, <1>2, PTL DEF Spec

=============================================================================