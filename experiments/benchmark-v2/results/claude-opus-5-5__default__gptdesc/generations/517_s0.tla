------------------------------- MODULE MCSession11b -------------------------------
(***************************************************************************)
(* Model-checking wrapper for the alternating-bit protocol specification  *)
(* in module Session11b.  It supplies:                                     *)
(*   - a concrete finite message set ConstData,                            *)
(*   - a state constraint bounding the lengths of channels AtoB and BtoA,  *)
(*   - state predicates for type correctness and simple invariants,        *)
(*   - ABSpecProperty, which is the Spec of the instantiated Session11a    *)
(*     module (the high-level ABSpec), checked as a temporal property.     *)
(*                                                                         *)
(* This module does not define its own transition relation.  Init, Next   *)
(* and Spec are inherited unchanged from Session11b.                       *)
(***************************************************************************)
EXTENDS Session11b, Integers, Sequences, FiniteSets

(***************************************************************************)
(* Concrete finite message set, substituted for constant Data in the model.*)
(***************************************************************************)
ConstData == {"d1", "d2", "d3"}

(***************************************************************************)
(* Bound on channel lengths, used as a state constraint.                   *)
(***************************************************************************)
MaxChanLen == 3

SeqConstraint == /\ Len(AtoB) =< MaxChanLen
                 /\ Len(BtoA) =< MaxChanLen

(***************************************************************************)
(* Type correctness of the communication state.                            *)
(***************************************************************************)
Msgs == Data \X {0, 1}

AB_TypeOK == /\ AVar \in Msgs
             /\ BVar \in Msgs
             /\ AtoB \in Seq(Msgs)
             /\ BtoA \in Seq({0, 1})

(***************************************************************************)
(* Simple invariant: every message in transit from A to B is either A's   *)
(* current value or B's current value.  Every bit in transit from B to A  *)
(* is either A's current bit or B's current bit.                           *)
(***************************************************************************)
AB_Inv == /\ AB_TypeOK
          /\ \A i \in 1..Len(AtoB) : AtoB[i] \in {AVar, BVar}
          /\ \A i \in 1..Len(BtoA) : BtoA[i] \in {AVar[2], BVar[2]}

(***************************************************************************)
(* A sequence is a "two-values sequence" if its entries change value at   *)
(* most once, i.e. it consists of a (possibly empty) block of one value   *)
(* followed by a (possibly empty) block of another value.                  *)
(***************************************************************************)
TwoValsSeq(s) ==
  \E k \in 0..Len(s) :
     /\ \A i, j \in 1..k : s[i] = s[j]
     /\ \A i, j \in (k+1)..Len(s) : s[i] = s[j]

Bits(s) == [i \in 1..Len(s) |-> s[i][2]]

AB_TwoValsSeq == /\ TwoValsSeq(Bits(AtoB))
                 /\ TwoValsSeq(BtoA)

(***************************************************************************)
(* The high-level specification from Session11a, instantiated with the    *)
(* identically named constants and variables of this module.               *)
(***************************************************************************)
ABS == INSTANCE Session11a

ABSpecProperty == ABS!Spec

(***************************************************************************)
(* Properties to check (with Spec inherited from Session11b):              *)
(*   INVARIANTS AB_TypeOK AB_Inv AB_TwoValsSeq                             *)
(*   PROPERTY   ABSpecProperty                                             *)
(*   CONSTRAINT SeqConstraint                                              *)
(***************************************************************************)
THEOREM Spec => [](AB_TypeOK /\ AB_Inv /\ AB_TwoValsSeq)
THEOREM Spec => ABSpecProperty
====================================================================================