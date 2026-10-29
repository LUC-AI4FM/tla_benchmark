---------------------------- MODULE MCSession11b ----------------------------
(***************************************************************************)
(* Model-checking wrapper around the implementation specification         *)
(* Session11b.  The implementation-level variables AVar2 and BVar2 are     *)
(* tuples <<data, bit>>; they are refined into the record-shaped abstract  *)
(* variables expected by Session11a.  Session11b is assumed to declare     *)
(* the constant Data, the variables AtoB, BtoA, AVar2 and BVar2, and to    *)
(* define Init, Next and Spec.                                              *)
(***************************************************************************)
EXTENDS Session11b, Naturals, Sequences

CONSTANT MaxSeqLen

ASSUME MaxSeqLen \in Nat

(***************************************************************************)
(* State constraint bounding the communication channels.                   *)
(***************************************************************************)
SeqConstraint == /\ Len(AtoB) <= MaxSeqLen
                 /\ Len(BtoA) <= MaxSeqLen

(***************************************************************************)
(* Type-correctness predicate for the refined implementation state.        *)
(***************************************************************************)
TypeOK2 == /\ AVar2 \in Data \X {0, 1}
           /\ BVar2 \in Data \X {0, 1}
           /\ AtoB \in Seq(Data \X {0, 1})
           /\ BtoA \in Seq({0, 1})

(***************************************************************************)
(* Refinement mapping: tuple-based variables to record-shaped variables.   *)
(***************************************************************************)
AVarBar == [data |-> AVar2[1], bit |-> AVar2[2]]
BVarBar == [data |-> BVar2[1], bit |-> BVar2[2]]

ABSpec == INSTANCE Session11a WITH AVar <- AVarBar, BVar <- BVarBar

(***************************************************************************)
(* The abstract specification property to be checked.                      *)
(***************************************************************************)
ABSpecProp == ABSpec!Spec
=============================================================================