------------------------------- MODULE SimpleRing -------------------------------
EXTENDS Naturals, TLAPS

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

(*--algorithm SimpleRing
variables x = [i \in 1..N |-> 0], y = [i \in 1..N |-> 0];

process Proc \in 1..N
begin
  s1: x[self] := 1;
  s2: y[self] := x[IF self = 1 THEN N ELSE self - 1];
end process;
end algorithm;
*)

\* BEGIN TRANSLATION
VARIABLES x, y, pc

vars == << x, y, pc >>

ProcSet == (1..N)

Init == (* Global variables *)
        /\ x = [i \in 1..N |-> 0]
        /\ y = [i \in 1..N |-> 0]
        /\ pc = [self \in ProcSet |-> "s1"]

s1(self) == /\ pc[self] = "s1"
            /\ x' = [x EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "s2"]
            /\ y' = y

s2(self) == /\ pc[self] = "s2"
            /\ y' = [y EXCEPT ![self] = x[IF self = 1 THEN N ELSE self - 1]]
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ x' = x

Proc(self) == s1(self) \/ s2(self)

Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..N: Proc(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

TypeOK == /\ x \in [1..N -> {0, 1}]
          /\ y \in [1..N -> {0, 1}]
          /\ pc \in [1..N -> {"s1", "s2", "Done"}]

LeftNeighbor(i) == IF i = 1 THEN N ELSE i - 1

PCorrect == (\A i \in 1..N : pc[i] = "Done") => (\E i \in 1..N : y[i] = 1)

Inv == /\ TypeOK
       /\ \A i \in 1..N : pc[i] \in {"s2", "Done"} => x[i] = 1
       /\ \A i \in 1..N : pc[i] = "Done" => y[i] = x[LeftNeighbor(i)]
       /\ (\A i \in 1..N : pc[i] = "Done") => (\E i \in 1..N : y[i] = 1)

THEOREM TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK
  BY NAssumption DEF Init, TypeOK, ProcSet
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  BY NAssumption DEF TypeOK, Next, Proc, s1, s2, Terminating, vars, ProcSet
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

THEOREM InvInductive == Spec => []Inv
<1>1. Init => Inv
  BY NAssumption DEF Init, Inv, TypeOK, ProcSet, LeftNeighbor
<1>2. Inv /\ [Next]_vars => Inv'
  <2>1. SUFFICES ASSUME Inv, [Next]_vars
               PROVE Inv'
    OBVIOUS
  <2>2. CASE \E self \in 1..N: s1(self)
    BY <2>1, <2>2, NAssumption DEF Inv, TypeOK, s1, LeftNeighbor, ProcSet
  <2>3. CASE \E self \in 1..N: s2(self)
    BY <2>1, <2>3, NAssumption DEF Inv, TypeOK, s2, LeftNeighbor, ProcSet
  <2>4. CASE Terminating
    BY <2>1, <2>4, NAssumption DEF Inv, TypeOK, Terminating, vars, ProcSet
  <2>5. CASE UNCHANGED vars
    BY <2>1, <2>5, NAssumption DEF Inv, TypeOK, vars, ProcSet
  <2>6. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next, Proc
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

THEOREM Safety == Spec => []PCorrect
<1>1. Inv => PCorrect
  BY DEF Inv, PCorrect
<1>2. QED
  BY InvInductive, <1>1, PTL

THEOREM SafetyAlt == Spec => []PCorrect
<1>1. Init => Inv
  BY NAssumption DEF Init, Inv, TypeOK, ProcSet, LeftNeighbor
<1>2. Inv /\ [Next]_vars => Inv'
  BY NAssumption DEF Inv, TypeOK, Next, Proc, s1, s2, Terminating, vars, ProcSet, LeftNeighbor
<1>3. Inv => PCorrect
  BY DEF Inv, PCorrect
<1>4. QED
  BY <1>1, <1>2, <1>3, PTL DEF Spec

=============================================================================