---------------------------- MODULE MCBinarySearch ----------------------------
(***************************************************************************)
(* Helper extension of BinarySearch for model checking. It introduces a    *)
(* bounded-sequence constructor so that the (otherwise infinite) set of    *)
(* sequences can be replaced by a finite set of sequences whose lengths    *)
(* are bounded by MaxSeqLen.                                               *)
(*                                                                         *)
(* The variables, Init, Next, Spec, invariants and liveness properties     *)
(* are inherited unchanged from BinarySearch. They are not redeclared      *)
(* here, because redefining them would be a multiple-definition error      *)
(* under SANY.                                                             *)
(***************************************************************************)
EXTENDS BinarySearch

CONSTANT MaxSeqLen

ASSUME MaxSeqLen \in Nat

LimitedSeq(S) == UNION { [1 .. n -> S] : n \in 1 .. MaxSeqLen }

=============================================================================