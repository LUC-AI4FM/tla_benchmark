---------------------------- MODULE SimpleRegular ----------------------------
EXTENDS Integers, TLAPS

CONSTANT N
ASSUME NAssump == (N \in Nat) /\ (N > 0)

(***************************************************************************
--algorithm SimpleRegular {
    variables x = [i \in 0..(N-1) |-> {0}], y = [i \in 0..(N-1) |-> 0] ;
    process (proc \in 0..N-1) {
      a1: x[self] := {0,1} ;
      a2: x[self] := {1} ;
      b:  with (v \in x[(self-1) % N]) { y[self] := v }
    }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES x, y, pc

vars == << x, y, pc >>

ProcSet == (0..N-1)

Init == (* Global variables *)
        /\ x = [i \in 0..(N-1) |-> {0}]
        /\ y = [i \in 0..(N-1) |-> 0]
        /\ pc = [self \in ProcSet |-> "a1"]

a1(self) == /\ pc[self] = "a1"
            /\ x' = [x EXCEPT ![self] = {0,1}]
            /\ pc' = [pc EXCEPT ![self] = "a2"]
            /\ y' = y

a2(self) == /\ pc[self] = "a2"
            /\ x' = [x EXCEPT ![self] = {1}]
            /\ pc' = [pc EXCEPT ![self] = "b"]
            /\ y' = y

b(self) == /\ pc[self] = "b"
           /\ \E v \in x[(self-1) % N]:
                y' = [y EXCEPT ![self] = v]
           /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ x' = x

proc(self) == a1(self) \/ a2(self) \/ b(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 0..N-1: proc(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
-----------------------------------------------------------------------------
PCorrect == (\A i \in 0..(N-1) : pc[i] = "Done") =>
                (\E i \in 0..(N-1) : y[i] = 1)

TypeOK == /\ x \in [0..(N-1) -> {{0}, {1}, {0,1}}]
          /\ y \in [0..(N-1) -> {0,1}]
          /\ pc \in [0..(N-1) -> {"a1", "a2", "b", "Done"}]

Inv == /\ TypeOK
       /\ \A i \in 0..(N-1) : (pc[i] \in {"b", "Done"}) => (x[i] = {1})
       /\ \/ \E i \in 0..(N-1) : pc[i] /= "Done"
          \/ \E i \in 0..(N-1) : y[i] = 1

LEMMA ModLemma == \A i \in 0..(N-1) : (i-1) % N \in 0..(N-1)
  BY NAssump

THEOREM InvInductive == Spec => []Inv
<1> USE NAssump
<1>1. Init => Inv
  BY DEF Init, Inv, TypeOK, ProcSet
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars
               PROVE  Inv'
    OBVIOUS
  <2>1. ASSUME NEW self \in 0..(N-1), a1(self)
        PROVE  Inv'
    BY <2>1 DEF a1, Inv, TypeOK
  <2>2. ASSUME NEW self \in 0..(N-1), a2(self)
        PROVE  Inv'
    BY <2>2 DEF a2, Inv, TypeOK
  <2>3. ASSUME NEW self \in 0..(N-1), b(self)
        PROVE  Inv'
    <3>1. (self-1) % N \in 0..(N-1)
      BY ModLemma
    <3>2. PICK v \in x[(self-1) % N] : y' = [y EXCEPT ![self] = v]
      BY <2>3 DEF b
    <3>3. TypeOK'
      BY <2>3, <3>1, <3>2 DEF b, Inv, TypeOK
    <3>4. (\A i \in 0..(N-1) : (pc[i] \in {"b", "Done"}) => (x[i] = {1}))'
      BY <2>3 DEF b, Inv, TypeOK
    <3>5. (\/ \E i \in 0..(N-1) : pc[i] /= "Done"
           \/ \E i \in 0..(N-1) : y[i] = 1)'
      <4>1. CASE \E i \in 0..(N-1) : i /= self /\ pc[i] /= "Done"
        BY <2>3, <4>1 DEF b, Inv, TypeOK
      <4>2. CASE \A i \in 0..(N-1) : i /= self => pc[i] = "Done"
        <5>1. pc[(self-1) % N] \in {"b", "Done"}
          BY <2>3, <3>1, <4>2 DEF b
        <5>2. x[(self-1) % N] = {1}
          BY <5>1, <3>1 DEF Inv
        <5>3. v = 1
          BY <3>2, <5>2
        <5>4. y'[self] = 1
          BY <3>2, <5>3 DEF Inv, TypeOK
        <5> QED
          BY <5>4
      <4> QED
        BY <4>1, <4>2
    <3> QED
      BY <3>3, <3>4, <3>5 DEF Inv
  <2>4. CASE Terminating
    BY <2>4 DEF Terminating, vars, Inv, TypeOK
  <2>5. CASE UNCHANGED vars
    BY <2>5 DEF vars, Inv, TypeOK
  <2> QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next, proc
<1> QED
  BY <1>1, <1>2, PTL DEF Spec

THEOREM Correctness == Spec => []PCorrect
<1>1. Inv => PCorrect
  BY DEF Inv, TypeOK, PCorrect
<1> QED
  BY <1>1, InvInductive, PTL
=============================================================================