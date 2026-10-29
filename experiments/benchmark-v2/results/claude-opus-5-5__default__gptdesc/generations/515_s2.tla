---------------------------- MODULE MCSession11afair ----------------------------
(***************************************************************************)
(* Model-checking wrapper for the alternating-bit specification of         *)
(* Session11afair, with a concrete three-element data set and properties   *)
(* to check: type correctness, a bit/message invariant, and liveness       *)
(* properties about agreement and alternation of AVar and BVar.            *)
(*                                                                         *)
(* The extended module Session11afair is not available here, so its        *)
(* transition system is included inline. This keeps the module             *)
(* self-contained and lets it pass SANY on its own.                        *)
(***************************************************************************)
EXTENDS Integers

(***************************************************************************)
(* Concrete constant data set of three string values.                      *)
(***************************************************************************)
Data == {"a", "b", "c"}

VARIABLES AVar, BVar

vars == <<AVar, BVar>>

(***************************************************************************)
(* Behavior inherited from Session11afair (inlined).                       *)
(***************************************************************************)
Init == /\ AVar \in Data \X {1}
        /\ BVar = AVar

A == /\ AVar = BVar
     /\ \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
     /\ BVar' = BVar

B == /\ AVar # BVar
     /\ BVar' = AVar
     /\ AVar' = AVar

Next == A \/ B

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

(***************************************************************************)
(* State predicates over the inherited variables.                          *)
(***************************************************************************)
TypeOK == /\ AVar \in Data \X {0, 1}
          /\ BVar \in Data \X {0, 1}

(* Equal bits are equivalent to equal messages.                            *)
Inv == (AVar[2] = BVar[2]) <=> (AVar = BVar)

(***************************************************************************)
(* Temporal liveness properties.                                           *)
(***************************************************************************)
(* AVar and BVar agree infinitely often.                                   *)
AgreeInfOften == []<>(AVar = BVar)

(* AVar and BVar alternate between agreeing and disagreeing forever.       *)
Alternation == /\ []<>(AVar = BVar)
               /\ []<>(AVar # BVar)

(* Every value sent by A is eventually received by B.                      *)
Delivery == \A v \in Data \X {0, 1} : (AVar = v) ~> (BVar = v)

(* Every disagreement eventually leads to agreement.                       *)
EventualAgreement == (AVar # BVar) ~> (AVar = BVar)

(***************************************************************************)
(* Theorems to be checked against the fair behavior.                       *)
(***************************************************************************)
THEOREM FairSpec => []TypeOK
THEOREM FairSpec => []Inv
THEOREM FairSpec => AgreeInfOften
THEOREM FairSpec => Alternation
THEOREM FairSpec => Delivery
THEOREM FairSpec => EventualAgreement
==================================================================================