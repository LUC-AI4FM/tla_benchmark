--------------------------- MODULE MCInnerSerial ---------------------------
(***************************************************************************)
(* Model-checking wrapper for the InnerSerial specification.               *)
(* The initial predicate, next-state relation and complete specification   *)
(* (with fairness) come from the extended module InnerSerial. They are not *)
(* redefined here, because redefining them would clash with the extended   *)
(* definitions.                                                            *)
(***************************************************************************)
EXTENDS InnerSerial, Naturals, Sequences

CONSTANT MaxQLen   \* Bound on the length of each process's operation queue

ASSUME MaxQLen \in Nat

(***************************************************************************)
(* A finite substitute for Nat, used by TLC in place of Nat.               *)
(***************************************************************************)
MCNat == 0..MaxQLen

(***************************************************************************)
(* An arbitrary initial memory, used for the constant parameter InitMem.   *)
(***************************************************************************)
MCInitMem == CHOOSE m \in [Adr -> Val] : TRUE

(***************************************************************************)
(* State constraint that keeps the state space finite.                     *)
(***************************************************************************)
Constraint == \A p \in Proc : Len(opQ[p]) =< MaxQLen

(***************************************************************************)
(* Liveness property:                                                      *)
(*   1. Every non-free register eventually becomes free again.             *)
(*   2. Every operation identifier in opId eventually corresponds to a     *)
(*      completed operation.                                               *)
(***************************************************************************)
AlwaysResponds ==
  /\ \A p \in Proc, r \in Reg :
        (regFile[p][r].op # "Free") ~> (regFile[p][r].op = "Free")
  /\ \A oi \in [proc : Proc, idx : MCNat] :
        (oi \in opId) ~> (/\ oi \in opId
                          /\ opQ[oi.proc][oi.idx].reg = "done")
=============================================================================