------------------------- MODULE MCInnerSequential -------------------------
(***************************************************************************)
(* Model-checking module for the InnerSequential specification.            *)
(*                                                                         *)
(* This module adds no actions of its own.  It relies on the extended      *)
(* module InnerSequential for the constants, variables, Init, Next and     *)
(* Spec, and for Proc, Reg, opQ and regFile.  Init, Next and Spec are not  *)
(* redefined here, because a second definition of an imported name is a    *)
(* SANY error.                                                             *)
(*                                                                         *)
(* It adds:                                                                *)
(*   - the constant MaxQLen, which bounds the length of each process's     *)
(*     operation queue,                                                    *)
(*   - a state constraint that keeps the reachable state space finite,     *)
(*   - a liveness property: every register entry that is not "Free"       *)
(*     eventually returns to "Free".                                       *)
(***************************************************************************)
EXTENDS InnerSequential

CONSTANT MaxQLen

ASSUME MaxQLen \in Nat

(***************************************************************************)
(* State constraint: no process's operation queue grows beyond MaxQLen.    *)
(***************************************************************************)
Constraint == \A p \in Proc : Len(opQ[p]) =< MaxQLen

(***************************************************************************)
(* Liveness: whenever a register entry of some process is not "Free", it   *)
(* eventually becomes "Free" again.                                        *)
(***************************************************************************)
AlwaysResponds ==
    \A p \in Proc, r \in Reg :
        (regFile[p][r] # "Free") ~> (regFile[p][r] = "Free")

=============================================================================