--------------------------- MODULE Simple ---------------------------
(***************************************************************************)
(* A simple concurrent ring algorithm.  There are N processes, numbered    *)
(* 0 through N-1, arranged in a ring.  Each process i first sets x[i] to   *)
(* 1 and then sets y[i] to the value of x[(i-1) % N], which is the x entry *)
(* of its left neighbor.  When every process has finished, at least one    *)
(* process i has y[i] = 1.                                                 *)
(***************************************************************************)
EXTENDS Integers, TLAPS

CONSTANT N

ASSUME NAssump == (N \in Nat) /\ (N > 0)

(***************************************************************************
--fair algorithm Simple {
    variables x = [i \in 0..(N-1) |-> 0],
              y = [i \in 0..(N-1) |-> 0] ;
    process (proc \in 0..(N-1)) {
      a: x[self] := 1 ;
      b: y[self] := x[(self-1) % N]
    }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES x, y, pc

vars == << x, y, pc >>

ProcSet == (0..(N-1))

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

Next == (\E self \in 0..(N-1) : proc(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

\* END TRANSLATION

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
(* First version of the proof.                                             *)
(***************************************************************************)
THEOREM Correctness == Spec => []PCorrect
<1> USE NAssump
<1>1. Init => Inv
  BY DEF Init, Inv, TypeOK, ProcSet
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv,
                      [Next]_vars
               PROVE  Inv'
    OBVIOUS
  <2>1. ASSUME NEW self \in 0..(N-1),
               a(self)
        PROVE  Inv'
    BY <2>1 DEF a, Inv, TypeOK
  <2>2. ASSUME NEW self \in 0..(N-1),
               b(self)
        PROVE  Inv'
    <3>1. ((self - 1) % N) \in 0..(N-1)
      OBVIOUS
    <3>2. QED
      BY <2>2, <3>1 DEF b, Inv, TypeOK
  <2>3. CASE UNCHANGED vars
    BY <2>3 DEF Inv, TypeOK, vars
  <2>4. QED
    BY <2>1, <2>2, <2>3 DEF Next, Terminating, proc
<1>3. Inv => PCorrect
  BY DEF Inv, TypeOK, PCorrect
<1>4. QED
  BY <1>1, <1>2, <1>3, PTL DEF Spec

-----------------------------------------------------------------------------
(***************************************************************************)
(* Second version of the proof, with a more detailed decomposition of the  *)
(* inductive step into the individual conjuncts of Inv.                    *)
(***************************************************************************)
THEOREM Correctness2 == Spec => []PCorrect
<1> USE NAssump
<1>1. Init => Inv
  <2> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <2>1. TypeOK
    BY DEF Init, TypeOK, ProcSet
  <2>2. \A i \in 0..(N-1) : (pc[i] \in {"b", "Done"}) => (x[i] = 1)
    BY DEF Init, ProcSet
  <2>3. \/ \E i \in 0..(N-1) : pc[i] /= "Done"
        \/ \E i \in 0..(N-1) : y[i] = 1
    <3>1. 0 \in 0..(N-1)
      OBVIOUS
    <3>2. QED
      BY <3>1 DEF Init, ProcSet
  <2>4. QED
    BY <2>1, <2>2, <2>3 DEF Inv
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv,
                      [Next]_vars
               PROVE  Inv'
    OBVIOUS
  <2> USE DEF Inv
  <2>1. CASE \E self \in 0..(N-1) : a(self)
    <3> SUFFICES ASSUME NEW self \in 0..(N-1), a(self)
                 PROVE  Inv'
      BY <2>1
    <3>1. TypeOK'
      BY DEF a, TypeOK
    <3>2. (\A i \in 0..(N-1) : (pc[i] \in {"b", "Done"}) => (x[i] = 1))'
      BY DEF a, TypeOK
    <3>3. (\/ \E i \in 0..(N-1) : pc[i] /= "Done"
           \/ \E i \in 0..(N-1) : y[i] = 1)'
      BY DEF a, TypeOK
    <3>4. QED
      BY <3>1, <3>2, <3>3
  <2>2. CASE \E self \in 0..(N-1) : b(self)
    <3> SUFFICES ASSUME NEW self \in 0..(N-1), b(self)
                 PROVE  Inv'
      BY <2>2
    <3>0. ((self - 1) % N) \in 0..(N-1)
      OBVIOUS
    <3>1. TypeOK'
      BY <3>0 DEF b, TypeOK
    <3>2. (\A i \in 0..(N-1) : (pc[i] \in {"b", "Done"}) => (x[i] = 1))'
      BY DEF b, TypeOK
    <3>3. (\/ \E i \in 0..(N-1) : pc[i] /= "Done"
           \/ \E i \in 0..(N-1) : y[i] = 1)'
      BY <3>0 DEF b, TypeOK
    <3>4. QED
      BY <3>1, <3>2, <3>3
  <2>3. CASE Terminating
    BY <2>3 DEF Terminating, vars, TypeOK
  <2>4. CASE UNCHANGED vars
    BY <2>4 DEF vars, TypeOK
  <2>5. QED
    BY <2>1, <2>2, <2>3, <2>4 DEF Next, proc
<1>3. Inv => PCorrect
  BY DEF Inv, TypeOK, PCorrect
<1>4. QED
  BY <1>1, <1>2, <1>3, PTL DEF Spec

=============================================================================