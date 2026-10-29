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

Init == /\ x = [i \in 0..(N-1) |-> {0}]
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
           /\ \E v \in x[(self-1) % N] :
                 y' = [y EXCEPT ![self] = v]
           /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ x' = x

proc(self) == a1(self) \/ a2(self) \/ b(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 0..N-1 : proc(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

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

THEOREM InvInductive == Spec => []Inv
<1> USE NAssump
<1>1. Init => Inv
  BY DEF Init, Inv, TypeOK, ProcSet
<1>2. Inv /\ [Next]_vars => Inv'
  BY DEF Inv, TypeOK, Next, Terminating, proc, a1, a2, b, vars, ProcSet
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

THEOREM Correctness == Spec => []PCorrect
<1> USE NAssump
<1>1. Init => Inv
  BY DEF Init, Inv, TypeOK, ProcSet
<1>2. Inv /\ [Next]_vars => Inv'
  BY DEF Inv, TypeOK, Next, Terminating, proc, a1, a2, b, vars, ProcSet
<1>3. Inv => PCorrect
  BY DEF Inv, TypeOK, PCorrect
<1>4. QED
  BY <1>1, <1>2, <1>3, PTL DEF Spec
=============================================================================