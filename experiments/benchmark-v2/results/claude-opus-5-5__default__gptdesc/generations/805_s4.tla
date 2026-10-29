---------------------------- MODULE MCBinarySearch ----------------------------
(***************************************************************************)
(* Model-checking helper for the BinarySearch module.  It introduces a     *)
(* bounded-sequence constructor so that TLC can enumerate a finite set of  *)
(* input sequences.  The Init, Next, Spec, invariants and any liveness     *)
(* properties are inherited unchanged from BinarySearch.                   *)
(***************************************************************************)
EXTENDS BinarySearch

CONSTANT MaxSeqLen

ASSUME MaxSeqLen \in Nat

LimitedSeq(S) == UNION { [1 .. n -> S] : n \in 1 .. MaxSeqLen }
=============================================================================