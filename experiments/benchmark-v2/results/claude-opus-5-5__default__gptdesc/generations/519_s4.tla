------------------------------ MODULE MCSession11b ------------------------------
(***************************************************************************)
(* Model-checking wrapper for the Session11b alternating bit protocol      *)
(* implementation. It bounds the channels AtoB and BtoA, defines a type    *)
(* invariant for the implementation state, and maps the tuple-valued       *)
(* variables AVar2 and BVar2 to the record-valued variables AVar and BVar  *)
(* of Session11a. It then instantiates Session11a with these substitutions *)
(* so that ABSpec!Spec can be checked as a property.                       *)
(***************************************************************************)
EXTENDS Session11b, Naturals, Sequences

CONSTANT MaxLen

ASSUME MaxLenAssump == MaxLen \in Nat

-----------------------------------------------------------------------------
(***************************************************************************)
(* State constraint that bounds the channel lengths for model checking.    *)
(***************************************************************************)
SeqConstraint == /\ Len(AtoB) \leq MaxLen
                 /\ Len(BtoA) \leq MaxLen

-----------------------------------------------------------------------------
(***************************************************************************)
(* Type-correctness predicate for the refined implementation state.        *)
(***************************************************************************)
TypeOKImpl == /\ AVar2 \in Data \X {0, 1}
              /\ BVar2 \in Data \X {0, 1}
              /\ AtoB  \in Seq(Data \X {0, 1})
              /\ BtoA  \in Seq({0, 1})

-----------------------------------------------------------------------------
(***************************************************************************)
(* Refinement mapping: tuples <<d, b>> become records [data |-> d, bit |-> b]. *)
(***************************************************************************)
AVarBar == [data |-> AVar2[1], bit |-> AVar2[2]]
BVarBar == [data |-> BVar2[1], bit |-> BVar2[2]]

ABSpec == INSTANCE Session11a WITH AVar <- AVarBar, BVar <- BVarBar

(***************************************************************************)
(* The property to be checked: the implementation refines Session11a.      *)
(***************************************************************************)
ABSpecProperty == ABSpec!Spec

=============================================================================