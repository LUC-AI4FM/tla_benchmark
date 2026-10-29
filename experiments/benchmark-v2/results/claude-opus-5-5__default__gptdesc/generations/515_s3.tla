------------------------------ MODULE MCSession11afair ------------------------------
(***************************************************************************)
(* Model-checking wrapper around Session11afair.  It does not define its   *)
(* own transition system: the behavior (Init, Next, Spec and the fair     *)
(* specification) is inherited from Session11afair, which declares the     *)
(* constant Data and the variables AVar and BVar.  This module only adds a *)
(* concrete data set and the state and temporal properties to check.      *)
(*                                                                         *)
(* Model configuration (TLC):                                              *)
(*   CONSTANT  Data <- MCData                                              *)
(*   SPECIFICATION  the fair specification of Session11afair               *)
(*   INVARIANTS     MCTypeOK  MCBitsInv                                    *)
(*   PROPERTIES     MCAgreement  MCAlternation  MCLeadsToAgreement         *)
(***************************************************************************)
EXTENDS Session11afair

(***************************************************************************)
(* Concrete data set of three string values, substituted for Data.         *)
(***************************************************************************)
MCData == {"a", "b", "c"}

(***************************************************************************)
(* Type correctness: each variable holds a message <<data, bit>>.          *)
(***************************************************************************)
MCTypeOK == /\ AVar \in Data \X {0, 1}
            /\ BVar \in Data \X {0, 1}

(***************************************************************************)
(* Invariant: the bits of AVar and BVar are equal if and only if the       *)
(* whole messages are equal.                                               *)
(***************************************************************************)
MCBitsInv == (AVar[2] = BVar[2]) <=> (AVar = BVar)

(***************************************************************************)
(* Liveness: AVar and BVar agree infinitely often.                         *)
(***************************************************************************)
MCAgreement == []<>(AVar = BVar)

(***************************************************************************)
(* Liveness: AVar and BVar alternate between agreeing and disagreeing      *)
(* infinitely often.                                                       *)
(***************************************************************************)
MCAlternation == /\ []<>(AVar = BVar)
                 /\ []<>(AVar # BVar)

(***************************************************************************)
(* Liveness: whenever AVar holds some message, BVar eventually holds that  *)
(* same message.                                                           *)
(***************************************************************************)
MCLeadsToAgreement == \A v \in Data \X {0, 1} : (AVar = v) ~> (BVar = v)

=====================================================================================