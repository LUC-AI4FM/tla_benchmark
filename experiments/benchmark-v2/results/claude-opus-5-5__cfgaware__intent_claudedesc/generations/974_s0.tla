------------------------------- MODULE RegularRegisters -------------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

ASSUME NAssump == N \in Nat /\ N > 0

Procs == 0 .. (N - 1)

Left(i) == (i - 1) % N

(***************************************************************************)
(* x[i] is the shared register of process i.  The register is regular, so  *)
(* it is modeled as the set of values that a read may return:              *)
(*   {0}     : the register stably holds 0                                 *)
(*   {0, 1}  : a write of 1 is in progress; a read may return 0 or 1       *)
(*   {1}     : the write has finished; the register stably holds 1         *)
(* y[i] is the private local register of process i.                        *)
(* pc[i] is the control state of process i.                                *)
(***************************************************************************)
VARIABLES x, y, pc

vars == << x, y, pc >>

TypeOK ==
    /\ x \in [Procs -> {{0}, {0, 1}, {1}}]
    /\ y \in [Procs -> {0, 1}]
    /\ pc \in [Procs -> {"a", "b", "c", "Done"}]

Init ==
    /\ x = [i \in Procs |-> {0}]
    /\ y = [i \in Procs |-> 0]
    /\ pc = [i \in Procs |-> "a"]

\* Begin writing 1: the register becomes transitional.
BeginWrite(i) ==
    /\ pc[i] = "a"
    /\ x' = [x EXCEPT ![i] = {0, 1}]
    /\ pc' = [pc EXCEPT ![i] = "b"]
    /\ UNCHANGED y

\* Complete the write: the register stably holds 1.
EndWrite(i) ==
    /\ pc[i] = "b"
    /\ x' = [x EXCEPT ![i] = {1}]
    /\ pc' = [pc EXCEPT ![i] = "c"]
    /\ UNCHANGED y

\* Read the left neighbor's register; any value it may currently return.
Read(i) ==
    /\ pc[i] = "c"
    /\ \E v \in x[Left(i)] :
          y' = [y EXCEPT ![i] = v]
    /\ pc' = [pc EXCEPT ![i] = "Done"]
    /\ UNCHANGED x

Proc(i) == BeginWrite(i) \/ EndWrite(i) \/ Read(i)

Terminating ==
    /\ \A i \in Procs : pc[i] = "Done"
    /\ UNCHANGED vars

Next == (\E i \in Procs : Proc(i)) \/ Terminating

Spec == Init /\ [][Next]_vars /\ \A i \in Procs : WF_vars(Proc(i))

-----------------------------------------------------------------------------
(* Safety property *)

PCorrect == (\A i \in Procs : pc[i] = "Done") => (\E i \in Procs : y[i] = 1)

(* Liveness property *)

Termination == <>(\A i \in Procs : pc[i] = "Done")

(* Inductive invariant *)

Inv ==
    /\ TypeOK
    /\ \A i \in Procs : pc[i] = "a" => x[i] = {0}
    /\ \A i \in Procs : pc[i] = "b" => x[i] = {0, 1}
    /\ \A i \in Procs : pc[i] \in {"c", "Done"} => x[i] = {1}
    /\ PCorrect

-----------------------------------------------------------------------------
(* Proof of the safety property via the inductive invariant Inv.           *)

THEOREM Safety == Spec => []PCorrect
<1>1. Init => Inv
  BY NAssump DEF Init, Inv, TypeOK, PCorrect, Procs
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <2>1. ASSUME NEW i \in Procs, BeginWrite(i) PROVE Inv'
    BY <2>1 DEF Inv, TypeOK, PCorrect, BeginWrite
  <2>2. ASSUME NEW i \in Procs, EndWrite(i) PROVE Inv'
    BY <2>2 DEF Inv, TypeOK, PCorrect, EndWrite
  <2>3. ASSUME NEW i \in Procs, Read(i) PROVE Inv'
    BY <2>3, NAssump DEF Inv, TypeOK, PCorrect, Read, Left, Procs
  <2>4. CASE Terminating
    BY <2>4 DEF Inv, TypeOK, PCorrect, Terminating, vars
  <2>5. CASE UNCHANGED vars
    BY <2>5 DEF Inv, TypeOK, PCorrect, vars
  <2>6. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next, Proc
<1>3. Inv => PCorrect
  BY DEF Inv
<1>4. QED
  BY <1>1, <1>2, <1>3 DEF Spec

THEOREM TypeCorrect == Spec => []TypeOK

THEOREM Liveness == Spec => Termination

=============================================================================