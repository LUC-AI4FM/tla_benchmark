---------------------------- MODULE MCInnerSequential ----------------------------
(***************************************************************************)
(* Adds a state constraint and a liveness property to the system defined  *)
(* in module InnerSequential. Init, Next, Spec, Proc, Reg, opQ and         *)
(* regFile all come from InnerSequential, so this module does not          *)
(* redefine them. This module contains no actions and no proofs.           *)
(***************************************************************************)
EXTENDS InnerSequential, Sequences

CONSTANT MaxQLen

(***************************************************************************)
(* State constraint: every process's operation queue has a length of at   *)
(* most MaxQLen.                                                           *)
(***************************************************************************)
Constraint == \A p \in Proc : Len(opQ[p]) <= MaxQLen

(***************************************************************************)
(* Liveness: whenever a register entry at some process is not "Free", it  *)
(* eventually returns to the "Free" state.                                 *)
(***************************************************************************)
AlwaysResponds ==
  \A p \in Proc, r \in Reg :
      (regFile[p][r].op # "Free") ~> (regFile[p][r].op = "Free")
=============================================================================