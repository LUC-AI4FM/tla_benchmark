------------------------------- MODULE RegularRegisters -------------------------------
(***************************************************************************)
(* N processes, numbered 0 .. N-1.  Each process i owns a shared register  *)
(* x[i] and a private local register y[i].  Process i executes:            *)
(*                                                                         *)
(*    a: begin writing 1 to x[i]   (x[i] enters a transitional state)      *)
(*    b: finish writing 1 to x[i]  (x[i] stably holds 1)                   *)
(*    c: y[i] := x[(i-1) % N]      (read the left neighbour's register)    *)
(*                                                                         *)
(* The shared registers are regular, not atomic.  A register value is      *)
(* modelled as the SET of values a read may currently return:              *)
(*    {0}    -- register stably holds 0 (initial value)                    *)
(*    {0,1}  -- a write of 1 over 0 is in progress; a read may return      *)
(*              either the old value 0 or the new value 1                  *)
(*    {1}    -- the write has completed; register stably holds 1           *)
(* A read nondeterministically chooses any element of that set.            *)
(*                                                                         *)
(* Safety: when all processes are done, some y[i] = 1.                     *)
(* Liveness: all processes eventually finish.                              *)
(* Check with TLC using e.g.  N <- 8,  INVARIANTS TypeOK Inv PCorrect,     *)
(* PROPERTY Termination.                                                   *)
(***************************************************************************)
EXTENDS Integers

CONSTANT N

ASSUME NAssump == N \in Nat \ {0}

ProcSet == 0 .. (N - 1)

Left(i) == (i - 1) % N

RegVals == {{0}, {0, 1}, {1}}

VARIABLES x, y, pc

vars == << x, y, pc >>

TypeOK ==
    /\ x  \in [ProcSet -> RegVals]
    /\ y  \in [ProcSet -> {0, 1}]
    /\ pc \in [ProcSet -> {"a", "b", "c", "done"}]

Init ==
    /\ x  = [i \in ProcSet |-> {0}]
    /\ y  = [i \in ProcSet |-> 0]
    /\ pc = [i \in ProcSet |-> "a"]

(* Begin writing 1: the register becomes "in transition" from 0 to 1. *)
a(i) ==
    /\ pc[i] = "a"
    /\ x'  = [x EXCEPT ![i] = {0, 1}]
    /\ pc' = [pc EXCEPT ![i] = "b"]
    /\ UNCHANGED y

(* Complete the write: the register now stably holds 1. *)
b(i) ==
    /\ pc[i] = "b"
    /\ x'  = [x EXCEPT ![i] = {1}]
    /\ pc' = [pc EXCEPT ![i] = "c"]
    /\ UNCHANGED y

(* Read the left neighbour's regular register: any value it may return. *)
c(i) ==
    /\ pc[i] = "c"
    /\ \E v \in x[Left(i)] : y' = [y EXCEPT ![i] = v]
    /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ UNCHANGED x

Proc(i) == a(i) \/ b(i) \/ c(i)

(* Allow stuttering after termination so the system does not deadlock. *)
Terminating ==
    /\ \A i \in ProcSet : pc[i] = "done"
    /\ UNCHANGED vars

Next == (\E i \in ProcSet : Proc(i)) \/ Terminating

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A i \in ProcSet : WF_vars(Proc(i))

---------------------------------------------------------------------------------------
(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)

(* Key safety property. *)
PCorrect == (\A i \in ProcSet : pc[i] = "done") => (\E i \in ProcSet : y[i] = 1)

(* Liveness: all processes eventually complete. *)
Termination == <>(\A i \in ProcSet : pc[i] = "done")

(* Inductive invariant. *)
Inv ==
    /\ TypeOK
    /\ \A i \in ProcSet : pc[i] \in {"c", "done"} => x[i] = {1}
    /\ PCorrect

---------------------------------------------------------------------------------------
(***************************************************************************)
(* Proof of the safety property via the inductive invariant Inv.           *)
(*                                                                         *)
(* Inductiveness argument for step c(j): if c(j) makes all processes done, *)
(* then before the step every other process was done and j was at "c".    *)
(* Hence the left neighbour l = Left(j) has pc[l] \in {"c","done"} (l = j  *)
(* when N = 1), so x[l] = {1}; the only value the read can return is 1,    *)
(* so y'[j] = 1.  Steps a and b cannot make all processes done, and no     *)
(* step other than i's own changes x[i].                                   *)
(***************************************************************************)

THEOREM InitInv == Init => Inv
  BY NAssump DEF Init, Inv, TypeOK, PCorrect, ProcSet, RegVals

THEOREM NextInv == Inv /\ [Next]_vars => Inv'
<1> SUFFICES ASSUME Inv, [Next]_vars
             PROVE  Inv'
  OBVIOUS
<1>1. ASSUME NEW i \in ProcSet, a(i)
      PROVE  Inv'
  BY NAssump DEF Inv, TypeOK, PCorrect, a, ProcSet, RegVals
<1>2. ASSUME NEW i \in ProcSet, b(i)
      PROVE  Inv'
  BY NAssump DEF Inv, TypeOK, PCorrect, b, ProcSet, RegVals
<1>3. ASSUME NEW i \in ProcSet, c(i)
      PROVE  Inv'
  <2>1. Left(i) \in ProcSet
    BY NAssump DEF Left, ProcSet
  <2>2. TypeOK'
    BY <2>1 DEF Inv, TypeOK, c, RegVals
  <2>3. (\A j \in ProcSet : pc[j] \in {"c", "done"} => x[j] = {1})'
    BY DEF Inv, TypeOK, c
  <2>4. PCorrect'
    <3>1. CASE \A j \in ProcSet : pc'[j] = "done"
      <4>1. pc[Left(i)] \in {"c", "done"}
        BY <2>1, <3>1 DEF Inv, TypeOK, c
      <4>2. x[Left(i)] = {1}
        BY <2>1, <4>1 DEF Inv
      <4>3. y'[i] = 1
        BY <4>2 DEF Inv, TypeOK, c
      <4>4. QED
        BY <4>3 DEF PCorrect
    <3>2. CASE ~(\A j \in ProcSet : pc'[j] = "done")
      BY <3>2 DEF PCorrect
    <3>3. QED
      BY <3>1, <3>2
  <2>5. QED
    BY <2>2, <2>3, <2>4 DEF Inv
<1>4. CASE Terminating
  BY <1>4 DEF Inv, TypeOK, PCorrect, Terminating, vars
<1>5. CASE UNCHANGED vars
  BY <1>5 DEF Inv, TypeOK, PCorrect, vars
<1>6. QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Next, Proc

THEOREM InvImpliesPCorrect == Inv => PCorrect
  BY DEF Inv

THEOREM Safety == Spec => []PCorrect
<1>1. Init => Inv
  BY InitInv
<1>2. Inv /\ [Next]_vars => Inv'
  BY NextInv
<1>3. Inv => PCorrect
  BY InvImpliesPCorrect
<1>4. QED
  BY <1>1, <1>2, <1>3 DEF Spec

THEOREM Liveness == Spec => Termination
  (* Each process takes at most three steps, each enabled until taken;   *)
  (* weak fairness of Proc(i) guarantees every process reaches "done".   *)
  (* Verified by TLC model checking for concrete N (e.g. N = 8).         *)
=======================================================================================