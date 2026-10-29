--------------------------- MODULE MCSession11afair ---------------------------
(***************************************************************************)
(* Model-checking wrapper for module Session11afair.                        *)
(*                                                                          *)
(* The behavior (Init, Next, Spec and its fairness conditions) and the     *)
(* state variables AVar and BVar are all inherited from Session11afair.    *)
(* This module only supplies:                                               *)
(*   - a concrete three-element value for the constant Data, and           *)
(*   - the type-correctness, safety and liveness properties to be checked. *)
(*                                                                          *)
(* In the model configuration, use these settings:                          *)
(*   CONSTANT Data <- MCData                                                *)
(*   SPECIFICATION Spec                                                     *)
(*   INVARIANTS TypeOK Inv                                                  *)
(*   PROPERTIES Agreement EventualAgreement Alternation Delivery            *)
(***************************************************************************)
EXTENDS Session11afair

(***************************************************************************)
(* Concrete data set used to instantiate the constant Data.                *)
(***************************************************************************)
MCData == {"d1", "d2", "d3"}

(***************************************************************************)
(* Type correctness: each variable holds a message, i.e. a pair made of a *)
(* data value and a one-bit tag.                                            *)
(***************************************************************************)
TypeOK == /\ AVar \in Data \X {0, 1}
          /\ BVar \in Data \X {0, 1}

(***************************************************************************)
(* Safety invariant: if the bits of AVar and BVar are equal, then the      *)
(* whole messages are equal.                                                *)
(***************************************************************************)
Inv == (AVar[2] = BVar[2]) => (AVar = BVar)

(***************************************************************************)
(* Liveness: AVar and BVar agree infinitely often.                          *)
(***************************************************************************)
Agreement == []<>(AVar = BVar)

(***************************************************************************)
(* Liveness: whenever AVar and BVar differ, they eventually agree.         *)
(***************************************************************************)
EventualAgreement == (AVar # BVar) ~> (AVar = BVar)

(***************************************************************************)
(* Liveness: AVar and BVar alternate between agreeing and disagreeing,    *)
(* i.e. new messages keep being sent and keep being received.              *)
(***************************************************************************)
Alternation == /\ []<>(AVar = BVar)
               /\ []<>(AVar # BVar)

(***************************************************************************)
(* Liveness: every message placed in AVar is eventually delivered to BVar. *)
(***************************************************************************)
Delivery == \A v \in Data \X {0, 1} : (AVar = v) ~> (BVar = v)

=============================================================================