-------------------------------- MODULE SimpleRing --------------------------------
EXTENDS Integers, TLAPS, FiniteSetTheorems

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

(* --algorithm SimpleRing
variables x = [i \in 1..N |-> 0], y = [i \in 1..N |-> 0];

process Proc \in 1..N
begin
  s1: x[self] := 1;
  s2: y[self] := x[(self - 2) % N + 1];
  s3: skip;
end process;
end algorithm *)

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
            /\ y' = [y EXCEPT ![self] = x[(self - 2) % N + 1]]
            /\ pc' = [pc EXCEPT ![self] = "s3"]
            /\ x' = x

s3(self) == /\ pc[self] = "s3"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << x, y >>

Proc(self) == s1(self) \/ s2(self) \/ s3(self)

Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..N: Proc(self))
           \/ Terminating

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in 1..N : WF_vars(Proc(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")
\* END TRANSLATION

\* Left neighbor function
Left(i) == (i - 2) % N + 1

\* Type correctness invariant
TypeOK == /\ x \in [1..N -> {0, 1}]
          /\ y \in [1..N -> {0, 1}]
          /\ pc \in [1..N -> {"s1", "s2", "s3", "Done"}]

\* All processes have completed
AllDone == \A i \in 1..N : pc[i] = "Done"

\* Safety property: when all done, at least one process has y[i] = 1
Safety == AllDone => \E i \in 1..N : y[i] = 1

\* Helper predicate: process i has set its x to 1
HasSetX(i) == pc[i] \in {"s2", "s3", "Done"}

\* Helper predicate: process i has read y from its left neighbor
HasSetY(i) == pc[i] \in {"s3", "Done"}

\* Inductive invariant components
Inv1 == TypeOK

Inv2 == \A i \in 1..N : HasSetX(i) => x[i] = 1

Inv3 == \A i \in 1..N : HasSetY(i) => (y[i] = 1 <=> HasSetX(Left(i)))

Inv4 == \A i \in 1..N : x[i] = 1 => HasSetX(i)

\* Main inductive invariant
Inv == Inv1 /\ Inv2 /\ Inv3 /\ Inv4

\* Strengthened invariant for proving safety
InvStrong == Inv /\ (AllDone => \E i \in 1..N : y[i] = 1)

\* THEOREM: Inv is inductive
THEOREM InvInit == Init => Inv
<1>1. Init => TypeOK
  BY NAssumption DEF Init, TypeOK, ProcSet
<1>2. Init => Inv2
  BY DEF Init, Inv2, HasSetX, ProcSet
<1>3. Init => Inv3
  BY DEF Init, Inv3, HasSetY, ProcSet
<1>4. Init => Inv4
  BY DEF Init, Inv4, HasSetX, ProcSet
<1>. QED BY <1>1, <1>2, <1>3, <1>4 DEF Inv

THEOREM InvInductive == Inv /\ [Next]_vars => Inv'
<1>. SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
  OBVIOUS
<1>1. CASE \E self \in 1..N: s1(self)
  <2>. PICK self \in 1..N : s1(self) BY <1>1
  <2>1. TypeOK' BY DEF Inv, TypeOK, s1
  <2>2. Inv2' BY DEF Inv, Inv1, Inv2, TypeOK, s1, HasSetX
  <2>3. Inv3' BY DEF Inv, Inv1, Inv3, TypeOK, s1, HasSetY
  <2>4. Inv4' BY DEF Inv, Inv1, Inv4, TypeOK, s1, HasSetX
  <2>. QED BY <2>1, <2>2, <2>3, <2>4 DEF Inv, Inv1
<1>2. CASE \E self \in 1..N: s2(self)
  <2>. PICK self \in 1..N : s2(self) BY <1>2
  <2>1. TypeOK' BY DEF Inv, Inv1, TypeOK, s2
  <2>2. Inv2' BY DEF Inv, Inv1, Inv2, TypeOK, s2, HasSetX
  <2>3. Inv3' BY DEF Inv, Inv1, Inv2, Inv3, TypeOK, s2, HasSetX, HasSetY, Left
  <2>4. Inv4' BY DEF Inv, Inv1, Inv4, TypeOK, s2, HasSetX
  <2>. QED BY <2>1, <2>2, <2>3, <2>4 DEF Inv, Inv1
<1>3. CASE \E self \in 1..N: s3(self)
  <2>. PICK self \in 1..N : s3(self) BY <1>3
  <2>1. TypeOK' BY DEF Inv, Inv1, TypeOK, s3
  <2>2. Inv2' BY DEF Inv, Inv1, Inv2, TypeOK, s3, HasSetX
  <2>3. Inv3' BY DEF Inv, Inv1, Inv3, TypeOK, s3, HasSetY, HasSetX
  <2>4. Inv4' BY DEF Inv, Inv1, Inv4, TypeOK, s3, HasSetX
  <2>. QED BY <2>1, <2>2, <2>3, <2>4 DEF Inv, Inv1
<1>4. CASE Terminating
  BY <1>4 DEF Inv, Inv1, Inv2, Inv3, Inv4, TypeOK, Terminating, vars, HasSetX, HasSetY
<1>5. CASE UNCHANGED vars
  BY <1>5 DEF Inv, Inv1, Inv2, Inv3, Inv4, TypeOK, vars, HasSetX, HasSetY
<1>. QED BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Next, Proc

\* THEOREM: Safety follows from Inv
THEOREM SafetyTheorem == Inv => Safety
<1>. SUFFICES ASSUME Inv, AllDone PROVE \E i \in 1..N : y[i] = 1
  BY DEF Safety
<1>1. 1 \in 1..N BY NAssumption
<1>2. HasSetX(1) BY <1>1 DEF AllDone, HasSetX
<1>3. x[1] = 1 BY <1>1, <1>2 DEF Inv, Inv2
<1>4. \E j \in 1..N : Left(j) = 1
  <2>. DEFINE j == (1 % N) + 1
  <2>1. j \in 1..N BY NAssumption
  <2>2. Left(j) = 1 BY NAssumption DEF Left
  <2>. QED BY <2>1, <2>2
<1>5. PICK j \in 1..N : Left(j) = 1 BY <1>4
<1>6. HasSetY(j) BY DEF AllDone, HasSetY
<1>7. y[j] = 1 <=> HasSetX(Left(j)) BY <1>6 DEF Inv, Inv3
<1>8. HasSetX(Left(j)) BY <1>5, <1>2
<1>9. y[j] = 1 BY <1>7, <1>8
<1>. QED BY <1>9

\* Main correctness theorem (version 1)
THEOREM Correctness1 == Spec => []Safety
<1>1. Init => Inv BY InvInit
<1>2. Inv /\ [Next]_vars => Inv' BY InvInductive
<1>3. Inv => Safety BY SafetyTheorem
<1>. QED BY <1>1, <1>2, <1>3, PTL DEF Spec

\* Main correctness theorem (version 2 - direct)  
THEOREM Correctness2 == Spec => [](AllDone => \E i \in 1..N : y[i] = 1)
<1>1. []Inv => []Safety BY SafetyTheorem, PTL
<1>2. Spec => []Inv BY InvInit, InvInductive, PTL DEF Spec
<1>. QED BY <1>1, <1>2, PTL DEF Safety

=============================================================================