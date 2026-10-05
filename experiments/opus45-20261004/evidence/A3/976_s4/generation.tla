------------------------------- MODULE simple -------------------------------
EXTENDS Naturals, TLAPS

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

(*
--algorithm Simple {
    variables x = [i \in 1..N |-> 0], y = [i \in 1..N |-> 0];
    process (proc \in 1..N) {
        a: x[self] := 1;
        b: y[self] := x[(self % N) + 1]
    }
}
*)

\* BEGIN TRANSLATION
VARIABLES x, y, pc

vars == << x, y, pc >>

ProcSet == (1..N)

Init == (* Global variables *)
        /\ x = [i \in 1..N |-> 0]
        /\ y = [i \in 1..N |-> 0]
        /\ pc = [self \in ProcSet |-> "a"]

a(self) == /\ pc[self] = "a"
           /\ x' = [x EXCEPT ![self] = 1]
           /\ pc' = [pc EXCEPT ![self] = "b"]
           /\ y' = y

b(self) == /\ pc[self] = "b"
           /\ y' = [y EXCEPT ![self] = x[(self % N) + 1]]
           /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ x' = x

proc(self) == a(self) \/ b(self)

Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..N: proc(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\* Type correctness invariant
TypeOK == /\ x \in [1..N -> {0, 1}]
          /\ y \in [1..N -> {0, 1}]
          /\ pc \in [1..N -> {"a", "b", "Done"}]

\* Safety property: when all processes are done, at least one has y[i] = 1
Safety == (\A i \in 1..N: pc[i] = "Done") => (\E i \in 1..N: y[i] = 1)

\* Inductive invariant
Inv == /\ TypeOK
       /\ \A i \in 1..N: (pc[i] \in {"b", "Done"}) => (x[i] = 1)
       /\ \A i \in 1..N: (pc[i] = "Done") => (y[i] = x[(i % N) + 1])
       /\ (\A i \in 1..N: pc[i] = "Done") => (\E i \in 1..N: x[i] = 1)

\* Helper: left neighbor function
Left(i) == (i % N) + 1

\* Theorem: Inv is inductive and implies Safety
THEOREM InvInductive == Spec => []Inv
<1>1. Init => Inv
  <2>1. Init => TypeOK
    BY NAssumption DEF Init, TypeOK, ProcSet
  <2>2. Init => \A i \in 1..N: (pc[i] \in {"b", "Done"}) => (x[i] = 1)
    BY DEF Init, ProcSet
  <2>3. Init => \A i \in 1..N: (pc[i] = "Done") => (y[i] = x[(i % N) + 1])
    BY DEF Init, ProcSet
  <2>4. Init => ((\A i \in 1..N: pc[i] = "Done") => (\E i \in 1..N: x[i] = 1))
    BY DEF Init, ProcSet
  <2>. QED BY <2>1, <2>2, <2>3, <2>4 DEF Inv
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <2>1. CASE \E self \in 1..N: a(self)
    BY <2>1, NAssumption DEF Inv, TypeOK, a, ProcSet
  <2>2. CASE \E self \in 1..N: b(self)
    BY <2>2, NAssumption DEF Inv, TypeOK, b, ProcSet
  <2>3. CASE Terminating
    BY <2>3 DEF Inv, TypeOK, Terminating, vars
  <2>4. CASE UNCHANGED vars
    BY <2>4 DEF Inv, TypeOK, vars
  <2>. QED BY <2>1, <2>2, <2>3, <2>4 DEF Next, proc
<1>. QED BY <1>1, <1>2, PTL DEF Spec

\* Theorem: Inv implies Safety
THEOREM InvImpliesSafety == Inv => Safety
<1> SUFFICES ASSUME Inv, \A i \in 1..N: pc[i] = "Done" PROVE \E i \in 1..N: y[i] = 1
  BY DEF Safety
<1>1. \E i \in 1..N: x[i] = 1
  BY DEF Inv
<1>2. PICK i \in 1..N: x[i] = 1
  BY <1>1
<1>3. \E j \in 1..N: Left(j) = i
  BY NAssumption DEF Left
<1>4. PICK j \in 1..N: Left(j) = i
  BY <1>3
<1>5. y[j] = x[Left(j)]
  BY DEF Inv, Left
<1>6. y[j] = x[i]
  BY <1>4, <1>5
<1>7. y[j] = 1
  BY <1>2, <1>6
<1>. QED BY <1>7

\* Main correctness theorem
THEOREM Correctness == Spec => []Safety
BY InvInductive, InvImpliesSafety, PTL

\* Alternative proof of correctness
THEOREM CorrectnessAlt == Spec => []Safety
<1>1. Init => Inv
  BY NAssumption DEF Init, Inv, TypeOK, ProcSet
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <2>1. CASE \E self \in 1..N: proc(self)
    <3> PICK self \in 1..N: proc(self)
      BY <2>1
    <3>1. CASE a(self)
      BY <3>1, NAssumption DEF Inv, TypeOK, a, ProcSet
    <3>2. CASE b(self)
      BY <3>2, NAssumption DEF Inv, TypeOK, b, ProcSet
    <3>. QED BY <3>1, <3>2 DEF proc
  <2>2. CASE Terminating
    BY <2>2 DEF Inv, TypeOK, Terminating, vars
  <2>. QED BY <2>1, <2>2 DEF Next
<1>3. Inv => Safety
  BY InvImpliesSafety
<1>. QED BY <1>1, <1>2, <1>3, PTL DEF Spec

=============================================================================