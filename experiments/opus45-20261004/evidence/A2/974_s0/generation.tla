---------------------------- MODULE RegularSimple ----------------------------
EXTENDS Integers, TLAPS, FiniteSets

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
           /\ \E v \in x[(self - 1) % N] : y' = [y EXCEPT ![self] = v]
           /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ x' = x

proc(self) == a1(self) \/ a2(self) \/ b(self)

Next == \E self \in Procs : proc(self)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in Procs : pc[self] = "Done")

PCorrect == (\A i \in Procs : pc[i] = "Done") => (\E i \in Procs : y[i] = 1)

WriteComplete == \A i \in Procs : pc[i] \in {"b", "Done"} => x[i] = {1}

NotDoneOrSomeOne == \/ \E i \in Procs : pc[i] # "Done"
                    \/ \E i \in Procs : y[i] = 1

Inv == TypeOK /\ WriteComplete /\ NotDoneOrSomeOne

THEOREM Correctness == Spec => []PCorrect
<1>1. Init => Inv
  <2>1. Init => TypeOK
    BY NAssumption DEF Init, TypeOK, Procs
  <2>2. Init => WriteComplete
    BY DEF Init, WriteComplete, Procs
  <2>3. Init => NotDoneOrSomeOne
    BY NAssumption DEF Init, NotDoneOrSomeOne, Procs
  <2>. QED
    BY <2>1, <2>2, <2>3 DEF Inv
<1>2. Inv /\ [Next]_vars => Inv'
  <2>1. SUFFICES ASSUME Inv, [Next]_vars
                 PROVE Inv'
    OBVIOUS
  <2>2. CASE UNCHANGED vars
    BY <2>1, <2>2 DEF Inv, TypeOK, WriteComplete, NotDoneOrSomeOne, vars
  <2>3. CASE Next
    <3>1. PICK self \in Procs : proc(self)
      BY <2>3 DEF Next
    <3>2. CASE a1(self)
      BY <2>1, <3>1, <3>2, NAssumption DEF Inv, TypeOK, WriteComplete, NotDoneOrSomeOne, a1, Procs
    <3>3. CASE a2(self)
      BY <2>1, <3>1, <3>3, NAssumption DEF Inv, TypeOK, WriteComplete, NotDoneOrSomeOne, a2, Procs
    <3>4. CASE b(self)
      <4>1. TypeOK'
        BY <2>1, <3>1, <3>4, NAssumption DEF Inv, TypeOK, b, Procs
      <4>2. WriteComplete'
        BY <2>1, <3>1, <3>4 DEF Inv, WriteComplete, b, Procs
      <4>3. NotDoneOrSomeOne'
        <5>1. CASE \E i \in Procs : i # self /\ pc[i] # "Done"
          BY <5>1, <3>4 DEF NotDoneOrSomeOne, b, Procs
        <5>2. CASE \A i \in Procs : i = self \/ pc[i] = "Done"
          <6>1. pc[(self - 1) % N] = "Done"
            BY <5>2, NAssumption DEF Procs
          <6>2. x[(self - 1) % N] = {1}
            BY <6>1, <2>1, NAssumption DEF Inv, WriteComplete, Procs
          <6>3. y'[self] = 1
            BY <3>4, <6>2 DEF b
          <6>. QED
            BY <6>3 DEF NotDoneOrSomeOne, Procs
        <5>. QED
          BY <5>1, <5>2
      <4>. QED
        BY <4>1, <4>2, <4>3 DEF Inv
    <3>. QED
      BY <3>1, <3>2, <3>3, <3>4 DEF proc
  <2>. QED
    BY <2>2, <2>3
<1>3. Inv => PCorrect
  BY DEF Inv, PCorrect, NotDoneOrSomeOne
<1>. QED
  BY <1>1, <1>2, <1>3, PTL DEF Spec

THEOREM Correctness2 == Spec => []PCorrect
<1>1. Init /\ [][Next]_vars => []Inv
  <2>1. Init => Inv
    BY DEF Init, Inv, TypeOK, WriteComplete, NotDoneOrSomeOne, Procs
  <2>2. Inv /\ [Next]_vars => Inv'
    BY DEF Inv, TypeOK, WriteComplete, NotDoneOrSomeOne, Next, proc, a1, a2, b, vars, Procs
  <2>. QED
    BY <2>1, <2>2, PTL
<1>2. []Inv => []PCorrect
  <2>1. Inv => PCorrect
    BY DEF Inv, PCorrect, NotDoneOrSomeOne
  <2>. QED
    BY <2>1, PTL
<1>. QED
  BY <1>1, <1>2, PTL DEF Spec

=============================================================================