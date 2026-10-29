---------------------------- MODULE MCSession11b ----------------------------
(***************************************************************************)
(* Model-checking wrapper for the implementation specification Session11b. *)
(* It bounds the lengths of the channels AtoB and BtoA, defines a type     *)
(* invariant for the implementation state, and refines the tuple-valued    *)
(* variables AVar2 and BVar2 into the record-valued variables AVar and     *)
(* BVar of the abstract specification Session11a.                          *)
(*                                                                         *)
(* Init, Next, Spec, the variables (AVar2, BVar2, AtoB, BtoA) and the      *)
(* constant Data all come from the extended module Session11b.  No local   *)
(* temporal behavior, fairness, or proofs are defined in this file.        *)
(***************************************************************************)
EXTENDS Session11b, Sequences, Naturals

CONSTANT CMaxLen   \* Upper bound on channel lengths used by the model checker

ASSUME CMaxLen \in Nat

(***************************************************************************)
(* State constraint for TLC: keep the channels bounded.                    *)
(***************************************************************************)
SeqConstraint == /\ Len(AtoB) =< CMaxLen
                 /\ Len(BtoA) =< CMaxLen

(***************************************************************************)
(* Type-correctness of the refined implementation state.                   *)
(***************************************************************************)
TypeOK2 == /\ AVar2 \in Data \X {0, 1}
           /\ BVar2 \in Data \X {0, 1}
           /\ AtoB  \in Seq(Data \X {0, 1})
           /\ BtoA  \in Seq({0, 1})

(***************************************************************************)
(* Refinement mapping: tuple-valued variables -> record-valued variables.  *)
(***************************************************************************)
AVarBar == [data |-> AVar2[1], bit |-> AVar2[2]]
BVarBar == [data |-> BVar2[1], bit |-> BVar2[2]]

ABSpec == INSTANCE Session11a WITH AVar <- AVarBar, BVar <- BVarBar

(***************************************************************************)
(* Property checked by TLC: the implementation refines the abstract spec.  *)
(***************************************************************************)
ABSpecProp == ABSpec!Spec
=============================================================================