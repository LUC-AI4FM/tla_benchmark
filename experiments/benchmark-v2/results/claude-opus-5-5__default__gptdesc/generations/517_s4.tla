---------------------------- MODULE MCSession11b ----------------------------
EXTENDS Session11b, Integers, Sequences, TLC

(***************************************************************************)
(* Model-checking wrapper for the specification in Session11b.             *)
(* This module defines no transition relation or temporal formula of its   *)
(* own. Init, Next and Spec come from Session11b.                          *)
(***************************************************************************)

(***************************************************************************)
(* A concrete finite message set, used to override the constant Data.      *)
(***************************************************************************)
ConstData == {"d1", "d2", "d3"}

(***************************************************************************)
(* State constraint that bounds the lengths of the two channels.           *)
(***************************************************************************)
MaxChanLen == 3

SeqConstraint == /\ Len(AtoB) <= MaxChanLen
                 /\ Len(BtoA) <= MaxChanLen

(***************************************************************************)
(* Type correctness of the communication state.                            *)
(***************************************************************************)
AB_TypeOK == /\ AVar \in Data \X {0, 1}
             /\ BVar \in Data \X {0, 1}
             /\ AtoB \in Seq(Data \X {0, 1})
             /\ BtoA \in Seq({0, 1})

(***************************************************************************)
(* IsTwoValSeq(s) holds when s consists of a (possibly empty) block of one *)
(* value followed by a (possibly empty) block of a second value.           *)
(***************************************************************************)
IsTwoValSeq(s) ==
  \E i \in 0..Len(s) :
     /\ \A j \in 1..i            : s[j] = s[1]
     /\ \A j \in (i+1)..Len(s)   : s[j] = s[Len(s)]

(***************************************************************************)
(* Every message and acknowledgement in transit, together with the         *)
(* senders' and receivers' current bits, forms a two-valued sequence.      *)
(***************************************************************************)
AB_TwoValsSeq ==
  LET bitsAtoB == [i \in 1..Len(AtoB) |-> AtoB[i][2]]
  IN  /\ IsTwoValSeq(<<AVar>> \o AtoB \o <<BVar>>)
      /\ IsTwoValSeq(<<AVar[2]>> \o bitsAtoB \o <<BVar[2]>> \o BtoA)

(***************************************************************************)
(* A simple invariant over the communication state.                        *)
(***************************************************************************)
AB_Inv ==
  /\ AB_TypeOK
  /\ \A i \in 1..Len(AtoB) :
        AtoB[i][2] = AVar[2] => AtoB[i] = AVar
  /\ (AVar[2] = BVar[2]) => (AVar = BVar)
  /\ AB_TwoValsSeq

(***************************************************************************)
(* Reference to the specification property of Session11a.                  *)
(***************************************************************************)
ABS == INSTANCE Session11a

ABSpecProperty == ABS!Spec

=============================================================================