---------------------------- MODULE MCBinarySearch ----------------------------
(***************************************************************************)
(* Helper module for model checking BinarySearch.                          *)
(*                                                                         *)
(* The variables, Init, Next, Spec, safety invariants, liveness            *)
(* properties and fairness conditions all come from the extended module    *)
(* BinarySearch. They are not declared or defined again here, because      *)
(* redefining them would be a multiple-definition error in SANY.           *)
(*                                                                         *)
(* This module adds only a bounded-sequence constructor. A model can use   *)
(* it in place of Seq(S) so the set of sequences is finite.                *)
(***************************************************************************)
EXTENDS BinarySearch

CONSTANT MaxSeqLen

ASSUME MaxSeqLen \in Nat

(***************************************************************************)
(* LimitedSeq(S) is the set of all nonempty sequences of elements of S     *)
(* whose length is at most MaxSeqLen.                                      *)
(***************************************************************************)
LimitedSeq(S) == UNION { [1 .. n -> S] : n \in 1 .. MaxSeqLen }

=============================================================================