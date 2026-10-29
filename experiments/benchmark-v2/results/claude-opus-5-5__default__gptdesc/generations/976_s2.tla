--------------------------- MODULE Simple ---------------------------
EXTENDS Integers, TLAPS

CONSTANT N
ASSUME NAssump == (N \in Nat) /\ (N > 0)

(****************************************************************************
--algorithm Simple {
    variables x = [i \in 0..(N-1) |-> 0], y = [i \in 0..(N-1) |-> 0] ;
    process (proc \in 0..N-1) {
      a: x[self] := 1 ;
      b: y[self] := x[(self-1) % N]
    }
}
****************************************************************************)
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
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 0..N-1: proc(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety property: when all processes are done, some y[i] equals 1.      *)
(***************************************************************************)
PCorrect == (\A i \in 0..(N-1) : pc[i] = "Done") =>
                (\E i \in 0..(N-1) : y[i] = 1)

TypeOK == /\ x \in [0..(N-1) -> {0,1}]
          /\ y \in [0..(N-1) -> {0,1}]
          /\ pc \in [0..(N-1) -> {"a", "b", "Done"}]

(***************************************************************************)
(* Inductive invariant.                                                    *)
(***************************************************************************)
Inv ==  /\ TypeOK
        /\ \A i \in 0..(N-1) : (pc[i] \in {"b", "Done"}) => (x[i] = 1)
        /\ \/ \E i \in 0..(N-1) : pc[i] /= "Done"
           \/ \E i \in 0..(N-1) : y[i] = 1

-----------------------------------------------------------------------------
(***************************************************************************)
(* First version of the proof.                                             *)
(***************************************************************************)
THEOREM Correctness == Spec => []PCorrect
<1>1. Init => Inv
  BY NAssump DEF Init, Inv, TypeOK, ProcSet
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv,
                      [Next]_vars
               PROVE  Inv'
    OBVIOUS
  <2>1. ASSUME NEW j \in 0..(N-1),
               a(j)
        PROVE  Inv'
    BY <2>1, NAssump DEF Inv, TypeOK, a, ProcSet
  <2>2. ASSUME NEW j \in 0..(N-1),
               b(j)
        PROVE  Inv'
    <3>1. (j-1) % N \in 0..(N-1)
      BY NAssump
    <3>2. TypeOK'
      BY <2>2, <3>1, NAssump DEF Inv, TypeOK, b
    <3>3. (\A i \in 0..(N-1) : (pc[i] \in {"b", "Done"}) => (x[i] = 1))'
      BY <2>2, NAssump DEF Inv, TypeOK, b
    <3>4. (\/ \E i \in 0..(N-1) : pc[i] /= "Done"
           \/ \E i \in 0..(N-1) : y[i] = 1)'
      BY <2>2, <3>1, NAssump DEF Inv, TypeOK, b
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

-----------------------------------------------------------------------------
(***************************************************************************)
(* Second version of the proof: first prove Inv is an invariant, then     *)
(* derive correctness from it.                                             *)
(***************************************************************************)
THEOREM InvInvariant == Spec => []Inv
<1>1. Init => Inv
  BY NAssump DEF Init, Inv, TypeOK, ProcSet
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv,
                      [Next]_vars
               PROVE  Inv'
    OBVIOUS
  <2>1. CASE \E self \in 0..N-1 : a(self)
    BY <2>1, NAssump DEF Inv, TypeOK, a, ProcSet
  <2>2. CASE \E self \in 0..N-1 : b(self)
    <3> SUFFICES ASSUME NEW j \in 0..(N-1), b(j)
                 PROVE  Inv'
      BY <2>2
    <3>1. (j-1) % N \in 0..(N-1)
      BY NAssump
    <3>2. QED
      BY <3>1, NAssump DEF Inv, TypeOK, b
  <2>3. CASE Terminating \/ UNCHANGED vars
    BY <2>3 DEF Inv, TypeOK, Terminating, vars
  <2>4. QED
    BY <2>1, <2>2, <2>3 DEF Next, proc
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

THEOREM Correctness2 == Spec => []PCorrect
<1>1. Inv => PCorrect
  BY DEF Inv, TypeOK, PCorrect
<1>2. QED
  BY <1>1, InvInvariant, PTL
=============================================================================