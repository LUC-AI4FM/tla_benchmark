---------------------------- MODULE MCSession11a ----------------------------
(***************************************************************************)
(* Model-checking companion for the Session11a specification.              *)
(* It supplies a concrete data set and defines the type-correctness        *)
(* condition and the bit-equality invariant over AVar and BVar.            *)
(* The underlying state structure (normally imported from Session11a) is   *)
(* reproduced here so that the module is self-contained.                   *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS d1, d2

(* Concrete constant data set used for model checking *)
const_Data == {d1, d2}

Data == const_Data

Msgs == [val : Data, bit : {0, 1}]

VARIABLES AVar, BVar

vars == <<AVar, BVar>>

-----------------------------------------------------------------------------
(* State structure from Session11a *)

Init ==
    /\ AVar \in Msgs
    /\ BVar = AVar

A ==
    /\ AVar = BVar
    /\ \E d \in Data :
          AVar' = [val |-> d, bit |-> 1 - AVar.bit]
    /\ UNCHANGED BVar

B ==
    /\ AVar /= BVar
    /\ BVar' = AVar
    /\ UNCHANGED AVar

Next == A \/ B

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Top-level state predicates *)

TypeOK ==
    /\ AVar \in Msgs
    /\ BVar \in Msgs

Inv ==
    (AVar.bit = BVar.bit) => (AVar = BVar)

-----------------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ Inv)
=============================================================================