------------------------------- MODULE Simple -------------------------------
(***************************************************************************)
(* A simple concurrent algorithm with N processes arranged in a ring.      *)
(* Process i first sets x[i] to 1, then sets y[i] to x[(i-1) % N], the     *)
(* x value of its left neighbor.  The algorithm is correct if, once every  *)
(* process has terminated, at least one process has y[i] = 1.              *)
(***************************************************************************)
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

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

\* END TRANSLATION

(***************************************************************************)
(* A weakly fair version of the specification, under which Termination    *)
(* holds.                                                                  *)
(***************************************************************************)
FairSpec == Spec /\ \A self \in 0..N-1 : WF_vars(proc(self))

(***************************************************************************)
(* The safety property: when all processes are done, some y[i] equals 1.   *)
(***************************************************************************)
PCorrect == (\A i \in 0..(N-1) : pc[i] = "Done") =>
                (\E i \in 0..(N-1) : y[i] = 1)

(***************************************************************************)
(* Type correctness.                                                       *)
(***************************************************************************)
TypeOK == /\ x \in [0..(N-1) -> {0, 1}]
          /\ y \in [0..(N-1) -> {0, 1}]
          /\ pc \in [0..(N-1) -> {"a", "b", "Done"}]

(***************************************************************************)
(* The inductive invariant.                                                *)
(***************************************************************************)
Inv == /\ TypeOK
       /\ \A i \in 0..(N-1) : (pc[i] \in {"b", "Done"}) => (x[i] = 1)
       /\ \/ \E i \in 0..(N-1) : pc[i] /= "Done"
          \/ \E i \in 0..(N-1) : y[i] = 1

-----------------------------------------------------------------------------
(***************************************************************************)
(* First version of the correctness proof: a flat proof.                   *)
(***************************************************************************)
THEOREM Correctness == Spec => []PCorrect
<1> USE NAssump
<1>1. Init => Inv
  BY DEF Init, Inv, TypeOK, ProcSet
<1>2. Inv /\ [Next]_vars => Inv'
  BY Z3 DEF Inv, TypeOK, Next, vars, proc, a, b, Terminating, ProcSet
<1>3. Inv => PCorrect
  BY DEF Inv, TypeOK, PCorrect
<1>4. QED
  BY <1>1, <1>2, <1>3, PTL DEF Spec

(***************************************************************************)
(* Second version of the correctness proof: a hierarchical proof.          *)
(***************************************************************************)
THEOREM Correctness2 == Spec => []PCorrect
<1> USE NAssump
<1>1. Init => Inv
  BY DEF Init, Inv, TypeOK, ProcSet
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars
               PROVE  Inv'
    OBVIOUS
  <2>1. ASSUME NEW self \in 0..N-1, a(self)
        PROVE  Inv'
    BY <2>1 DEF Inv, TypeOK, a
  <2>2. ASSUME NEW self \in 0..N-1, b(self)
        PROVE  Inv'
    <3>1. (self - 1) % N \in 0..(N-1)
      OBVIOUS
    <3>2. TypeOK'
      BY <2>2, <3>1 DEF Inv, TypeOK, b
    <3>3. (\A i \in 0..(N-1) : (pc[i] \in {"b", "Done"}) => (x[i] = 1))'
      BY <2>2 DEF Inv, TypeOK, b
    <3>4. (\/ \E i \in 0..(N-1) : pc[i] /= "Done"
           \/ \E i \in 0..(N-1) : y[i] = 1)'
      <4>1. CASE \E i \in 0..(N-1) : pc'[i] /= "Done"
        BY <4>1
      <4>2. CASE \A i \in 0..(N-1) : pc'[i] = "Done"
        <5>1. pc[(self - 1) % N] \in {"b", "Done"}
          BY <2>2, <3>1, <4>2 DEF Inv, TypeOK, b
        <5>2. x[(self - 1) % N] = 1
          BY <5>1, <3>1 DEF Inv
        <5>3. y'[self] = 1
          BY <2>2, <5>2 DEF Inv, TypeOK, b
        <5>4. QED
          BY <5>3
      <4>3. QED
        BY <4>1, <4>2
    <3>5. QED
      BY <3>2, <3>3, <3>4 DEF Inv
  <2>3. CASE Terminating
    BY <2>3 DEF Inv, TypeOK, Terminating, vars
  <2>4. CASE UNCHANGED vars
    BY <2>4 DEF Inv, TypeOK, vars
  <2>5. QED
    BY <2>1, <2>2, <2>3, <2>4 DEF Next, proc
<1>3. Inv => PCorrect
  BY DEF Inv, TypeOK, PCorrect
<1>4. QED
  BY <1>1, <1>2, <1>3, PTL DEF Spec

=============================================================================