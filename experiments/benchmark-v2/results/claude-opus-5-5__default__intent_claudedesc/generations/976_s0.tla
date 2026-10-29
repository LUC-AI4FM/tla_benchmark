------------------------------ MODULE CircleWrite ------------------------------
(***************************************************************************)
(* N processes, numbered 0..N-1 and arranged in a circle. Each process i  *)
(* runs two steps:                                                         *)
(*    a:  x[i] := 1                                                        *)
(*    b:  y[i] := x[(i-1) mod N]                                           *)
(* Both x and y start as all zeros. Once every process has terminated, at *)
(* least one entry of y must equal 1.                                      *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N

ASSUME NAssump == N \in Nat \ {0}

Procs == 0 .. (N - 1)

Left(i) == (i + N - 1) % N

VARIABLES x, y, pc

vars == << x, y, pc >>

-----------------------------------------------------------------------------
Init == /\ x  = [i \in Procs |-> 0]
        /\ y  = [i \in Procs |-> 0]
        /\ pc = [i \in Procs |-> "a"]

a(i) == /\ pc[i] = "a"
        /\ x' = [x EXCEPT ![i] = 1]
        /\ pc' = [pc EXCEPT ![i] = "b"]
        /\ UNCHANGED y

b(i) == /\ pc[i] = "b"
        /\ y' = [y EXCEPT ![i] = x[Left(i)]]
        /\ pc' = [pc EXCEPT ![i] = "Done"]
        /\ UNCHANGED x

proc(i) == a(i) \/ b(i)

(* Allows infinite stuttering after termination, so it is not a deadlock. *)
Terminating == /\ \A i \in Procs : pc[i] = "Done"
               /\ UNCHANGED vars

Next == (\E i \in Procs : proc(i)) \/ Terminating

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A i \in Procs : WF_vars(proc(i))

-----------------------------------------------------------------------------
(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
AllDone == \A i \in Procs : pc[i] = "Done"

TypeOK == /\ x  \in [Procs -> {0, 1}]
          /\ y  \in [Procs -> {0, 1}]
          /\ pc \in [Procs -> {"a", "b", "Done"}]

(* Postcondition, stated as a safety invariant. *)
PCorrect == AllDone => (\E i \in Procs : y[i] = 1)

(* Liveness: every process eventually terminates. *)
Termination == <>AllDone

(***************************************************************************)
(* Inductive invariant.                                                    *)
(*  - Any process that has executed step a has x[i] = 1.                  *)
(*  - Either some process has not finished, or some y[i] equals 1.        *)
(* When the last process i executes b, every other process (in particular *)
(* Left(i), or i itself if N = 1) has passed step a. So x[Left(i)] = 1,  *)
(* and therefore y[i] becomes 1. This keeps the second conjunct true.     *)
(***************************************************************************)
Inv == /\ TypeOK
       /\ \A i \in Procs : pc[i] \in {"b", "Done"} => x[i] = 1
       /\ (\E i \in Procs : pc[i] /= "Done") \/ (\E i \in Procs : y[i] = 1)

THEOREM InvImpliesPCorrect == Inv => PCorrect
THEOREM InitInv == Init => Inv
THEOREM InvInductive == Inv /\ [Next]_vars => Inv'
THEOREM SafetyThm == Spec => []PCorrect
THEOREM InvThm == Spec => []Inv
THEOREM LivenessThm == Spec => Termination
=============================================================================