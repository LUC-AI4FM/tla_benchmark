------------------------------- MODULE MCSession11a -------------------------------
(***************************************************************************)
(* Model-checking companion module for the Session11a specification.       *)
(* It supplies a concrete data set and two state predicates: TypeOK and    *)
(* an invariant that equal bit fields imply equal message records.         *)
(*                                                                         *)
(* So that this module parses on its own with SANY, the state structure    *)
(* that would come from Session11a is declared here: the variables AVar    *)
(* and BVar, the message set Msgs, and minimal Init, Next and Spec         *)
(* definitions.                                                            *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT Data

VARIABLES AVar, BVar

vars == <<AVar, BVar>>

(***************************************************************************)
(* Concrete data set used for model checking (substituted for Data).       *)
(***************************************************************************)
MCData == {"d1", "d2"}

(***************************************************************************)
(* Message records: a data value tagged with an alternating bit.          *)
(***************************************************************************)
Msgs == [val : Data, bit : {0, 1}]

----------------------------------------------------------------------------
(***************************************************************************)
(* State structure assumed from Session11a.                                *)
(***************************************************************************)
Init ==
  /\ AVar \in Msgs
  /\ BVar = AVar

(* A sends a new message by choosing a value and flipping the bit. *)
A ==
  /\ AVar = BVar
  /\ \E d \in Data : AVar' = [val |-> d, bit |-> 1 - AVar.bit]
  /\ UNCHANGED BVar

(* B receives the message by copying it. *)
B ==
  /\ AVar # BVar
  /\ BVar' = AVar
  /\ UNCHANGED AVar

Next == A \/ B

Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------
(***************************************************************************)
(* Type-correctness: AVar and BVar are both elements of Msgs.              *)
(***************************************************************************)
TypeOK ==
  /\ AVar \in Msgs
  /\ BVar \in Msgs

(***************************************************************************)
(* Invariant: if the bit fields of AVar and BVar are equal, then the two   *)
(* message records are equal.                                              *)
(***************************************************************************)
Inv ==
  (AVar.bit = BVar.bit) => (AVar = BVar)

=============================================================================