---------------------------- MODULE MCInnerSequential ----------------------------
(***************************************************************************)
(* This module adds a state constraint and a liveness property to the      *)
(* system specified in module InnerSequential.  Init, Next and Spec, along *)
(* with Proc, Reg, opQ and regFile, are all defined in InnerSequential.    *)
(* They are inherited through EXTENDS and are not redefined here, because  *)
(* redefining them would be a multiple-definition error in SANY.           *)
(***************************************************************************)
EXTENDS InnerSequential

CONSTANT MaxQLen

ASSUME MaxQLenAssump == MaxQLen \in Nat

(***************************************************************************)
(* State constraint: every process's operation queue has length at most    *)
(* MaxQLen.                                                                *)
(***************************************************************************)
Constraint == \A p \in Proc : Len(opQ[p]) \leq MaxQLen

(***************************************************************************)
(* Liveness: whenever a register entry at some process is not "Free", it   *)
(* eventually becomes "Free" again.                                        *)
(***************************************************************************)
AlwaysResponds ==
  \A p \in Proc, r \in Reg :
     (regFile[p][r].op # "Free") ~> (regFile[p][r].op = "Free")

=============================================================================