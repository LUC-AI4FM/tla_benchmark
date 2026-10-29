---------------------------- MODULE MCSession11b ----------------------------
(***************************************************************************)
(* Model-checking wrapper around the implementation specification          *)
(* Session11b.  It bounds the lengths of the channels AtoB and BtoA,       *)
(* defines a type-correctness predicate for the refined implementation     *)
(* state, and maps the tuple-valued implementation variables AVar2 and     *)
(* BVar2 into the record-shaped abstract variables AVar and BVar (with     *)
(* fields data and bit) expected by Session11a.  The instantiated          *)
(* abstract specification ABSpec!Spec is exposed as the property to be     *)
(* checked.  Init, Next and Spec come from the extended module             *)
(* Session11b; no local temporal behavior, fairness or proofs are defined  *)
(* here.                                                                   *)
(***************************************************************************)
EXTENDS Session11b, Naturals, Sequences

CONSTANT MaxSeqLen

ASSUME MaxSeqLen \in Nat

(***************************************************************************)
(* State constraint for model checking: bounded channel lengths.           *)
(***************************************************************************)
SeqConstraint ==
    /\ Len(AtoB) =< MaxSeqLen
    /\ Len(BtoA) =< MaxSeqLen

(***************************************************************************)
(* Type correctness of the refined implementation state.                   *)
(***************************************************************************)
TypeOKImpl ==
    /\ AVar2 \in Data \X {0, 1}
    /\ BVar2 \in Data \X {0, 1}
    /\ AtoB  \in Seq(Data \X {0, 1})
    /\ BtoA  \in Seq({0, 1})

(***************************************************************************)
(* Refinement mapping: tuples <<d, b>> become records [data |-> d,         *)
(* bit |-> b].                                                             *)
(***************************************************************************)
AVarBar == [data |-> AVar2[1], bit |-> AVar2[2]]
BVarBar == [data |-> BVar2[1], bit |-> BVar2[2]]

ABSpec == INSTANCE Session11a WITH AVar <- AVarBar, BVar <- BVarBar

(***************************************************************************)
(* Property to be checked: the implementation refines the abstract spec.   *)
(***************************************************************************)
ABSpecProperty == ABSpec!Spec

=============================================================================