---------------------------- MODULE MCBinarySearch ----------------------------
(***************************************************************************)
(* Model-checking helper for BinarySearch.                                 *)
(*                                                                         *)
(* This module extends BinarySearch and adds a bounded-sequence            *)
(* constructor, LimitedSeq(S). It is the set of all non-empty sequences   *)
(* over S whose length is at most MaxSeqLen. A TLC model can substitute    *)
(* it for the unbounded Seq(S), for example when defining the set of       *)
(* input sequences BinarySearch ranges over.                               *)
(*                                                                         *)
(* The CONSTANTS, VARIABLES, Init, Next and Spec, together with the        *)
(* safety invariants, liveness properties and fairness conditions, all     *)
(* come from BinarySearch through EXTENDS. Defining them again here would  *)
(* cause a multiple-definition error in SANY, so this module only adds     *)
(* the constant MaxSeqLen and the operator LimitedSeq.                     *)
(***************************************************************************)
EXTENDS BinarySearch

CONSTANT MaxSeqLen

ASSUME MaxSeqLen \in Nat

LimitedSeq(S) == UNION { [1 .. n -> S] : n \in 1 .. MaxSeqLen }

=============================================================================