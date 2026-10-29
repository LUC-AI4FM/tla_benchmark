---- MODULE SimpleRegular ----
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
       /\ \A i \in 0..(N-1) : (pc[i] = "a2") => (1 \in x[i])
       /\ \/ \E i \in 0..(N-1) : pc[i] /= "Done"
          \/ \E i \in 0..(N-1) : y[i] = 1

THEOREM InvInductive == Spec => []Inv
<1>1. Init => Inv
  BY NAssump DEF Init, Inv, TypeOK, ProcSet
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <2>1. ASSUME NEW self \in 0..(N-1), a1(self) PROVE Inv'
    BY <2>1, NAssump DEF Inv, TypeOK, a1
  <2>2. ASSUME NEW self \in 0..(N-1), a2(self) PROVE Inv'
    BY <2>2, NAssump DEF Inv, TypeOK, a2
  <2>3. ASSUME NEW self \in 0..(N-1), b(self) PROVE Inv'
    <3>1. (self-1) % N \in 0..(N-1)
      BY NAssump
    <3>2. QED
      BY <2>3, <3>1, NAssump DEF Inv, TypeOK, b
  <2>4. CASE Terminating
    BY <2>4 DEF Inv, TypeOK, Terminating, vars
  <2>5. CASE UNCHANGED vars
    BY <2>5 DEF Inv, TypeOK, vars
  <2>6. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next, proc
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

THEOREM Correctness == Spec => []PCorrect
<1>1. Inv => PCorrect
  BY DEF Inv, TypeOK, PCorrect
<1>2. QED
  BY <1>1, InvInductive, PTL
=============================================================================