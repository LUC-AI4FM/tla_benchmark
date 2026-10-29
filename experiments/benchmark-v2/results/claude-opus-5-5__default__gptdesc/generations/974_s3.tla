---------------------------- MODULE SimpleRegular ----------------------------
EXTENDS Integers, TLAPS

CONSTANT N
ASSUME NAssump == (N \in Nat) /\ (N > 0)

(***************************************************************************
--algorithm SimpleRegular {
    variables x = [i \in 0..(N-1) |-> {0}], y = [i \in 0..(N-1) |-> 0] ;
    process (proc \in 0..N-1) {
      s1: x[self] := {0,1} ;
      s2: x[self] := {1} ;
      s3: with (v \in x[(self-1) % N]) { y[self] := v }
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
        /\ pc = [self \in ProcSet |-> "s1"]

s1(self) == /\ pc[self] = "s1"
            /\ x' = [x EXCEPT ![self] = {0,1}]
            /\ pc' = [pc EXCEPT ![self] = "s2"]
            /\ y' = y

s2(self) == /\ pc[self] = "s2"
            /\ x' = [x EXCEPT ![self] = {1}]
            /\ pc' = [pc EXCEPT ![self] = "s3"]
            /\ y' = y

s3(self) == /\ pc[self] = "s3"
            /\ \E v \in x[(self-1) % N]:
                 y' = [y EXCEPT ![self] = v]
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ x' = x

proc(self) == s1(self) \/ s2(self) \/ s3(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 0..N-1: proc(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

PCorrect == (\A i \in 0..(N-1) : pc[i] = "Done") =>
                (\E i \in 0..(N-1) : y[i] = 1)

TypeOK == /\ x \in [0..(N-1) -> {{0}, {1}, {0,1}}]
          /\ y \in [0..(N-1) -> {0,1}]
          /\ pc \in [0..(N-1) -> {"s1", "s2", "s3", "Done"}]

Inv == /\ PCorrect
       /\ TypeOK
       /\ \A i \in 0..(N-1) : (pc[i] \in {"s2", "s3", "Done"}) => (1 \in x[i])
       /\ \A i \in 0..(N-1) : (pc[i] \in {"s3", "Done"}) => (x[i] = {1})

LEMMA ModLemma == \A i \in 0..(N-1) : (i-1) % N \in 0..(N-1)
  BY NAssump

THEOREM InvInductive == Spec => []Inv
<1> USE NAssump DEF ProcSet
<1>1. Init => Inv
  BY DEF Init, Inv, TypeOK, PCorrect
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <2>1. ASSUME NEW self \in 0..(N-1), s1(self) PROVE Inv'
    BY <2>1 DEF s1, Inv, TypeOK, PCorrect
  <2>2. ASSUME NEW self \in 0..(N-1), s2(self) PROVE Inv'
    BY <2>2 DEF s2, Inv, TypeOK, PCorrect
  <2>3. ASSUME NEW self \in 0..(N-1), s3(self) PROVE Inv'
    <3>1. (self-1) % N \in 0..(N-1)
      BY ModLemma
    <3>2. PICK v \in x[(self-1) % N] : y' = [y EXCEPT ![self] = v]
      BY <2>3 DEF s3
    <3>3. v \in {0,1}
      BY <3>1 DEF Inv, TypeOK
    <3>4. TypeOK'
      BY <2>3, <3>2, <3>3 DEF s3, Inv, TypeOK
    <3>5. PCorrect'
      <4> SUFFICES ASSUME \A i \in 0..(N-1) : pc'[i] = "Done"
                   PROVE  \E i \in 0..(N-1) : y'[i] = 1
        BY DEF PCorrect
      <4>1. pc[(self-1) % N] \in {"s3", "Done"}
        BY <2>3, <3>1 DEF s3, Inv, TypeOK
      <4>2. x[(self-1) % N] = {1}
        BY <4>1, <3>1 DEF Inv
      <4>3. v = 1
        BY <4>2, <3>2
      <4>4. y'[self] = 1
        BY <3>2, <4>3 DEF Inv, TypeOK
      <4> QED
        BY <4>4
    <3>6. (\A i \in 0..(N-1) : (pc[i] \in {"s2", "s3", "Done"}) => (1 \in x[i]))'
      BY <2>3 DEF s3, Inv, TypeOK
    <3>7. (\A i \in 0..(N-1) : (pc[i] \in {"s3", "Done"}) => (x[i] = {1}))'
      BY <2>3 DEF s3, Inv, TypeOK
    <3> QED
      BY <3>4, <3>5, <3>6, <3>7 DEF Inv
  <2>4. CASE Terminating
    BY <2>4 DEF Terminating, vars, Inv, TypeOK, PCorrect
  <2>5. CASE UNCHANGED vars
    BY <2>5 DEF vars, Inv, TypeOK, PCorrect
  <2>6. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next, proc
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

THEOREM Correctness == Spec => []PCorrect
<1>1. Inv => PCorrect
  BY DEF Inv
<1>2. QED
  BY <1>1, InvInductive, PTL
=============================================================================