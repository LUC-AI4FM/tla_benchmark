---------------------------- MODULE SimpleRegular ----------------------------
(***************************************************************************)
(* N processes communicate through single-writer regular registers.        *)
(* Each process self executes:                                             *)
(*   a1: begin writing 1 to x[self]   (x[self] := x[self] \cup {1})        *)
(*   a2: complete the write           (x[self] := {1})                     *)
(*   b : read x[(self-1) % N] and store the value read in y[self]          *)
(* A regular register is modelled by the set of values a read may return.  *)
(* While a write is in progress, the set holds both the old value and the  *)
(* value being written. When the write completes, the set is {new value}.  *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANT N

ASSUME NAssump == (N \in Nat) /\ (N > 0)

VARIABLES x, y, pc

vars == << x, y, pc >>

ProcSet == 0 .. (N - 1)

PCStates == {"a1", "a2", "b", "Done"}

LeftNeighbor(self) == (self - 1) % N

Init ==
    /\ x  = [i \in ProcSet |-> {0}]
    /\ y  = [i \in ProcSet |-> 0]
    /\ pc = [self \in ProcSet |-> "a1"]

(* Begin writing value 1: the register may now return the old value or 1 *)
a1(self) ==
    /\ pc[self] = "a1"
    /\ x' = [x EXCEPT ![self] = x[self] \cup {1}]
    /\ pc' = [pc EXCEPT ![self] = "a2"]
    /\ UNCHANGED y

(* Complete the write: the register now contains exactly 1 *)
a2(self) ==
    /\ pc[self] = "a2"
    /\ x' = [x EXCEPT ![self] = {1}]
    /\ pc' = [pc EXCEPT ![self] = "b"]
    /\ UNCHANGED y

(* Read the left neighbor's register: any value in its possible-value set *)
b(self) ==
    /\ pc[self] = "b"
    /\ \E v \in x[LeftNeighbor(self)] :
          y' = [y EXCEPT ![self] = v]
    /\ pc' = [pc EXCEPT ![self] = "Done"]
    /\ UNCHANGED x

proc(self) == a1(self) \/ a2(self) \/ b(self)

(* Allow infinite stuttering once all processes have terminated *)
Terminating ==
    /\ \A self \in ProcSet : pc[self] = "Done"
    /\ UNCHANGED vars

Next == (\E self \in ProcSet : proc(self)) \/ Terminating

Spec == Init /\ [][Next]_vars

(* Fair version: every process keeps taking steps while it can *)
FairSpec == Spec /\ \A self \in ProcSet : WF_vars(proc(self))

-----------------------------------------------------------------------------
(* Type invariant *)
TypeOK ==
    /\ x  \in [ProcSet -> (SUBSET {0, 1}) \ {{}}]
    /\ y  \in [ProcSet -> {0, 1}]
    /\ pc \in [ProcSet -> PCStates]

(* Safety: if all processes have terminated, some process read 1 *)
PCorrect ==
    (\A p \in ProcSet : pc[p] = "Done") => (\E p \in ProcSet : y[p] = 1)

(* Inductive invariant suitable for proving PCorrect *)
Inv ==
    /\ TypeOK
    /\ \A i \in ProcSet :
          /\ (pc[i] \in {"a2", "b", "Done"}) => (1 \in x[i])
          /\ (pc[i] \in {"b", "Done"}) => (x[i] = {1})
    /\ PCorrect
    /\ (\A p \in ProcSet : pc[p] = "Done") \/
       (\E p \in ProcSet : pc[p] # "Done") 
    /\ (\A p \in ProcSet : pc[p] \in {"b", "Done"}) =>
          \/ \E p \in ProcSet : pc[p] = "b"
          \/ \E p \in ProcSet : y[p] = 1

(* Liveness: all processes eventually terminate *)
Termination == <>(\A self \in ProcSet : pc[self] = "Done")

THEOREM Spec => []TypeOK
THEOREM Spec => []PCorrect
THEOREM FairSpec => Termination
=============================================================================