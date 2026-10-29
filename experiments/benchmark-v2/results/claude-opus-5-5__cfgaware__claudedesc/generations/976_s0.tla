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
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 0..N-1: proc(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

PCorrect == (\A i \in 0..(N-1) : pc[i] = "Done") =>
                (\E i \in 0..(N-1) : y[i] = 1)

TypeOK == /\ x \in [0..(N-1) -> {0,1}]
          /\ y \in [0..(N-1) -> {0,1}]
          /\ pc \in [0..(N-1) -> {"a", "b", "Done"}]

Inv ==  /\ TypeOK
        /\ \A i \in 0..(N-1) : (pc[i] \in {"b", "Done"}) => (x[i] = 1)
        /\ \/ \E i \in 0..(N-1) : pc[i] /= "Done"
           \/ \E i \in 0..(N-1) : y[i] = 1

THEOREM Correctness == Spec => []PCorrect
<1>1. Init => Inv
  BY NAssump DEF Init, Inv, TypeOK, ProcSet
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv,
                      [Next]_vars
               PROVE  Inv'
    OBVIOUS
  <2>1. ASSUME NEW self \in 0..(N-1),
               a(self)
        PROVE  Inv'
    BY <2>1, NAssump DEF Inv, TypeOK, a
  <2>2. ASSUME NEW self \in 0..(N-1),
               b(self)
        PROVE  Inv'
    <3>1. ((self-1) % N) \in 0..(N-1)
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
    BY <2>3 DEF Terminating, Inv, TypeOK, vars
  <2>4. CASE UNCHANGED vars
    BY <2>4 DEF Inv, TypeOK, vars
  <2>5. QED
    BY <2>1, <2>2, <2>3, <2>4 DEF Next, proc
<1>3. Inv => PCorrect
  BY DEF Inv, TypeOK, PCorrect
<1>4. QED
  BY <1>1, <1>2, <1>3, PTL DEF Spec

THEOREM Correctness2 == Spec => []PCorrect
<1>1. Init => Inv
  BY NAssump DEF Init, Inv, TypeOK, ProcSet
<1>2. Inv /\ [Next]_vars => Inv'
  BY NAssump DEF Inv, TypeOK, Next, proc, a, b, Terminating, vars, ProcSet
<1>3. Inv => PCorrect
  BY DEF Inv, TypeOK, PCorrect
<1>4. QED
  BY <1>1, <1>2, <1>3, PTL DEF Spec
=============================================================================