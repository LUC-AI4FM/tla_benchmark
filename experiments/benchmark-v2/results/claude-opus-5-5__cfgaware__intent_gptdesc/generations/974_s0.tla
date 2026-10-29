---------------------------- MODULE RegularSimple ----------------------------
EXTENDS Naturals

CONSTANT N

ASSUME NAssump == N \in Nat \ {0}

Procs == 0..(N-1)

Left(i) == IF i = 0 THEN N - 1 ELSE i - 1

(* x[i] : set of values a read of register i may currently return          *)
(* y[i] : local storage of process i                                       *)
(* pc[i]: control state of process i                                       *)
VARIABLES x, y, pc

vars == <<x, y, pc>>

ControlStates == {"a1", "a2", "b", "Done"}

TypeOK ==
  /\ x  \in [Procs -> (SUBSET {0, 1}) \ {{}}]
  /\ y  \in [Procs -> {0, 1}]
  /\ pc \in [Procs -> ControlStates]

Init ==
  /\ x  = [i \in Procs |-> {0}]
  /\ y  = [i \in Procs |-> 0]
  /\ pc = [i \in Procs |-> "a1"]

(* Begin writing value A = 1: an overlapping read may now return 1 or the  *)
(* previous value(s).                                                      *)
a1(self) ==
  /\ pc[self] = "a1"
  /\ x' = [x EXCEPT ![self] = @ \cup {1}]
  /\ pc' = [pc EXCEPT ![self] = "a2"]
  /\ UNCHANGED y

(* Complete the write: the register now definitely contains 1.            *)
a2(self) ==
  /\ pc[self] = "a2"
  /\ x' = [x EXCEPT ![self] = {1}]
  /\ pc' = [pc EXCEPT ![self] = "b"]
  /\ UNCHANGED y

(* Read the left neighbour's register: nondeterministically obtain any     *)
(* value it may currently hold under regular-register semantics.          *)
b(self) ==
  /\ pc[self] = "b"
  /\ \E v \in x[Left(self)] : y' = [y EXCEPT ![self] = v]
  /\ pc' = [pc EXCEPT ![self] = "Done"]
  /\ UNCHANGED x

proc(self) == a1(self) \/ a2(self) \/ b(self)

Terminating ==
  /\ \A self \in Procs : pc[self] = "Done"
  /\ UNCHANGED vars

Next == (\E self \in Procs : proc(self)) \/ Terminating

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(proc(self))

AllDone == \A i \in Procs : pc[i] = "Done"

(* Safety: if all processes have terminated, some process read 1.         *)
PCorrect == AllDone => \E i \in Procs : y[i] = 1

(* Termination: all processes eventually terminate.                       *)
Termination == <>AllDone

(* Inductive invariant                                                     *)
Inv ==
  /\ TypeOK
  /\ \A i \in Procs : pc[i] \in {"b", "Done"} => x[i] = {1}
  /\ PCorrect

THEOREM Spec => []PCorrect
THEOREM Spec => Termination
=============================================================================