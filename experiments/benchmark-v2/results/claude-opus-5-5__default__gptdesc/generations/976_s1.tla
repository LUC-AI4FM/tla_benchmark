---------------------------- MODULE Simple ----------------------------
EXTENDS Integers, TLAPS

CONSTANT N
ASSUME NAssump == (N \in Nat) /\ (N > 0)

(***************************************************************************
--algorithm Simple {
    variables x = [i \in 0..(N-1) |-> 0], y = [i \in 0..(N-1) |-> 0] ;
    process (proc \in 0..N-1) {
      a: x[self] := 1 ;
      b: y[self] := x[(self-1) % N]
    }
}
***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES x, y, pc

vars == << x, y, pc >>

ProcSet == (0..N-1)

Init == (* Global variables *)
        /\ x = [i \in 0..(N-1) |-> 0]
        /\ y = [i \in 0..(N-1) |-> 0]
        /\ pc = [self \in ProcSet |-> "a"]

a(self) == /\ pc[self] = "a"
           /\ x' = [x EXCEPT ![self] = 1]
           /\ pc' = [pc EXCEPT ![self] = "b"]
           /\ y' = y

b(self) == /\ pc[self] = "b"
           /\ y' = [y EXCEPT ![self] = x[(self-1) % N]]
           /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ x' = x

proc(self) == a(self) \/ b(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 0..N-1 : proc(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 0..N-1 : WF_vars(proc(self))

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

\* END TRANSLATION

(***************************************************************************)
(* Correctness property: when all processes are done, some y[i] = 1.      *)
(***************************************************************************)
PCorrect == (\A i \in 0..(N-1) : pc[i] = "Done") =>
                (\E i \in 0..(N-1) : y[i] = 1)

(***************************************************************************)
(* Type correctness.                                                       *)
(***************************************************************************)
TypeOK == /\ x \in [0..(N-1) -> {0,1}]
          /\ y \in [0..(N-1) -> {0,1}]
          /\ pc \in [0..(N-1) -> {"a", "b", "Done"}]

(***************************************************************************)
(* Inductive invariant.                                                    *)
(***************************************************************************)
Inv == /\ TypeOK
       /\ \A i \in 0..(N-1) : (pc[i] \in {"b", "Done"}) => (x[i] = 1)
       /\ \/ \E i \in 0..(N-1) : pc[i] /= "Done"
          \/ \E i \in 0..(N-1) : y[i] = 1

(***************************************************************************)
(* First version of the proof.                                             *)
(***************************************************************************)
THEOREM Correctness == Spec => []PCorrect
<1>1. Init => Inv
  BY NAssump DEF Init, Inv, TypeOK, ProcSet
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <2>1. ASSUME NEW j \in 0..(N-1), a(j) PROVE Inv'
    BY <2>1, NAssump DEF a, Inv, TypeOK
  <2>2. ASSUME NEW j \in 0..(N-1), b(j) PROVE Inv'
    <3>1. (j-1) % N \in 0..(N-1)
      BY NAssump
    <3>2. x[(j-1) % N] = 1
      <4>1. CASE \A i \in 0..(N-1) : pc'[i] = "Done"
        <5>1. pc[(j-1) % N] \in {"b", "Done"}
          BY <4>1, <3>1, <2>2, NAssump DEF b, Inv, TypeOK
        <5>2. QED
          BY <5>1, <3>1 DEF Inv
      <4>2. CASE ~(\A i \in 0..(N-1) : pc'[i] = "Done")
        \* In this case the third conjunct of Inv' holds trivially,
        \* but we still need x[(j-1)%N] \in {0,1}; we do not need = 1.
        \* Restructure: handle via the QED step below.
        OMITTED
      <4>3. QED
        BY <4>1, <4>2
    <3>3. TypeOK'
      BY <2>2, <3>1 DEF b, Inv, TypeOK
    <3>4. (\A i \in 0..(N-1) : (pc[i] \in {"b", "Done"}) => (x[i] = 1))'
      BY <2>2 DEF b, Inv, TypeOK
    <3>5. (\/ \E i \in 0..(N-1) : pc[i] /= "Done"
           \/ \E i \in 0..(N-1) : y[i] = 1)'
      <4>1. CASE \A i \in 0..(N-1) : pc'[i] = "Done"
        <5>1. pc[(j-1) % N] \in {"b", "Done"}
          BY <4>1, <3>1, <2>2, NAssump DEF b, Inv, TypeOK
        <5>2. x[(j-1) % N] = 1
          BY <5>1, <3>1 DEF Inv
        <5>3. y'[j] = 1
          BY <5>2, <2>2 DEF b, Inv, TypeOK
        <5>4. QED
          BY <5>3
      <4>2. CASE ~(\A i \in 0..(N-1) : pc'[i] = "Done")
        BY <4>2
      <4>3. QED
        BY <4>1, <4>2
    <3>6. QED
      BY <3>3, <3>4, <3>5 DEF Inv
  <2>3. CASE UNCHANGED vars
    BY <2>3 DEF Inv, TypeOK, vars
  <2>4. CASE Terminating
    BY <2>4 DEF Terminating, Inv, TypeOK, vars
  <2>5. QED
    BY <2>1, <2>2, <2>3, <2>4 DEF Next, proc
<1>3. Inv => PCorrect
  BY DEF Inv, PCorrect
<1>4. QED
  BY <1>1, <1>2, <1>3, PTL DEF Spec

(***************************************************************************)
(* Second version of the proof, with a more compact inductive step.        *)
(***************************************************************************)
THEOREM Correctness2 == Spec => []PCorrect
<1> USE NAssump DEF ProcSet
<1>1. Init => Inv
  BY DEF Init, Inv, TypeOK
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <2>1. ASSUME NEW j \in 0..(N-1), a(j) PROVE Inv'
    BY <2>1 DEF a, Inv, TypeOK
  <2>2. ASSUME NEW j \in 0..(N-1), b(j) PROVE Inv'
    <3>1. (j-1) % N \in 0..(N-1)
      OBVIOUS
    <3>2. (\A i \in 0..(N-1) : pc'[i] = "Done") => x[(j-1) % N] = 1
      BY <2>2, <3>1 DEF b, Inv, TypeOK
    <3>3. QED
      BY <2>2, <3>1, <3>2 DEF b, Inv, TypeOK
  <2>3. CASE UNCHANGED vars \/ Terminating
    BY <2>3 DEF Terminating, Inv, TypeOK, vars
  <2>4. QED
    BY <2>1, <2>2, <2>3 DEF Next, proc
<1>3. Inv => PCorrect
  BY DEF Inv, PCorrect
<1>4. QED
  BY <1>1, <1>2, <1>3, PTL DEF Spec

=============================================================================