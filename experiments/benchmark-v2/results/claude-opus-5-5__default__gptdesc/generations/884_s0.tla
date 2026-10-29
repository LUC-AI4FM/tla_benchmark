--------------------------- MODULE MCInnerSequential ---------------------------
(***************************************************************************)
(* Model-checking module for the InnerSequential specification.            *)
(*                                                                         *)
(* It adds:                                                                *)
(*   - a constant MaxQLen bounding the length of every process's           *)
(*     operation queue, expressed as a state constraint, and               *)
(*   - a liveness property asserting that every register-file entry that   *)
(*     is not "Free" eventually becomes "Free" again.                      *)
(*                                                                         *)
(* Init, Next and Spec are inherited from the extended module              *)
(* InnerSequential. Redefining them here would be a multiple-definition    *)
(* error, so this module adds no actions. The constants and variables are  *)
(* also inherited: Proc and Reg are constants, and opQ and regFile are     *)
(* variables.                                                              *)
(***************************************************************************)
EXTENDS InnerSequential

CONSTANT MaxQLen

ASSUME MaxQLen \in Nat

(***************************************************************************)
(* State constraint: every process's operation queue has length at most    *)
(* MaxQLen.                                                                *)
(***************************************************************************)
Constraint == \A p \in Proc : Len(opQ[p]) \leq MaxQLen

(***************************************************************************)
(* Liveness: whenever register r of process p is not in the "Free" state,  *)
(* it eventually returns to the "Free" state.                              *)
(***************************************************************************)
AlwaysResponds ==
  \A p \in Proc, r \in Reg :
     (regFile[p][r].op # "Free") ~> (regFile[p][r].op = "Free")

=============================================================================