---------------------------- MODULE MCSession11afair ----------------------------
EXTENDS Session11afair

(***************************************************************************)
(* Concrete data set for model checking. In the TLC configuration, the     *)
(* constant Data of Session11afair is overridden by MCData:                *)
(*     CONSTANT Data <- MCData                                             *)
(***************************************************************************)
MCData == {"a", "b", "c"}

(***************************************************************************)
(* Type correctness of the inherited state variables AVar and BVar. Each   *)
(* is a message: a pair consisting of a data value and a bit.              *)
(***************************************************************************)
TypeOK == /\ AVar \in Data \X {0, 1}
          /\ BVar \in Data \X {0, 1}

(***************************************************************************)
(* Invariant: if the bits of AVar and BVar are equal, then the whole       *)
(* messages are equal.                                                     *)
(***************************************************************************)
Inv == (AVar[2] = BVar[2]) => (AVar = BVar)

(***************************************************************************)
(* Liveness: AVar and BVar agree infinitely often.                         *)
(***************************************************************************)
Agreement == []<>(AVar = BVar)

(***************************************************************************)
(* Liveness: AVar and BVar alternate between agreement and disagreement   *)
(* forever, i.e., the sender keeps sending new messages and the receiver   *)
(* keeps catching up.                                                      *)
(***************************************************************************)
Alternation == /\ []<>(AVar = BVar)
               /\ []<>(AVar # BVar)

(***************************************************************************)
(* Liveness: every message value held by AVar is eventually received in   *)
(* BVar.                                                                   *)
(***************************************************************************)
EventuallyReceived == \A v \in Data \X {0, 1} : (AVar = v) ~> (BVar = v)

(***************************************************************************)
(* Properties to be checked against the fair specification FairSpec       *)
(* defined in Session11afair.                                              *)
(***************************************************************************)
THEOREM FairSpec => []TypeOK
THEOREM FairSpec => []Inv
THEOREM FairSpec => Agreement
THEOREM FairSpec => Alternation
THEOREM FairSpec => EventuallyReceived
=============================================================================