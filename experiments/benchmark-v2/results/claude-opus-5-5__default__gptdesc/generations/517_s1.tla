---------------------------- MODULE MCSession11 ----------------------------
(***************************************************************************)
(* Model-checking wrapper for the alternating-bit protocol specification  *)
(* defined in Session11b.  It supplies a concrete finite data set, a      *)
(* state constraint bounding the lengths of the channels AtoB and BtoA,   *)
(* type-correctness and invariant predicates, and the high-level property *)
(* ABSpecProperty, which is the Spec of the instantiated Session11a.      *)
(*                                                                         *)
(* Session11b is assumed to declare CONSTANT Data and the VARIABLES       *)
(* AVar, BVar, AtoB, BtoA, and to define Init, Next and Spec.  Session11a *)
(* is assumed to declare CONSTANT Data and VARIABLES AVar, BVar, so they  *)
(* are instantiated implicitly by the identically named symbols here.     *)
(***************************************************************************)
EXTENDS Session11b, Naturals, Sequences

CONSTANTS a, b, c

(***************************************************************************)
(* Concrete finite message set, substituted for Data in the model.        *)
(***************************************************************************)
ConstData == {a, b, c}

(***************************************************************************)
(* State constraint bounding the lengths of the two channels.             *)
(***************************************************************************)
SeqConstraint == /\ Len(AtoB) <= 3
                 /\ Len(BtoA) <= 3

(***************************************************************************)
(* Type correctness of the communication state.                           *)
(***************************************************************************)
AB_TypeOK == /\ AVar \in Data \X {0, 1}
             /\ BVar \in Data \X {0, 1}
             /\ AtoB \in Seq(Data \X {0, 1})
             /\ BtoA \in Seq({0, 1})

(***************************************************************************)
(* AB_TwoValsSeq(s) is true iff the sequence s consists of a (possibly    *)
(* empty) block of one value followed by a (possibly empty) block of a    *)
(* second value, i.e. its value changes at most once.                     *)
(***************************************************************************)
AB_TwoValsSeq(s) ==
  \E k \in 0..Len(s) :
     /\ \A i \in 1..k : s[i] = s[1]
     /\ \A i \in (k+1)..Len(s) : s[i] = s[Len(s)]

(***************************************************************************)
(* The sequence of bits carried by the messages in AtoB.                  *)
(***************************************************************************)
AB_AtoBBits == [i \in 1..Len(AtoB) |-> AtoB[i][2]]

(***************************************************************************)
(* Simple inductive-style invariant over the communication state.         *)
(***************************************************************************)
AB_Inv ==
  /\ AB_TypeOK
  /\ AB_TwoValsSeq(<<BVar[2]>> \o AB_AtoBBits \o <<AVar[2]>>)
  /\ AB_TwoValsSeq(<<AVar[2]>> \o BtoA \o <<BVar[2]>>)
  /\ \A i \in 1..Len(AtoB) :
        AtoB[i][2] = AVar[2] => AtoB[i] = AVar
  /\ (AVar[2] = BVar[2]) => (AVar = BVar)

(***************************************************************************)
(* The high-level specification that the protocol should implement.       *)
(***************************************************************************)
ABS == INSTANCE Session11a

ABSpecProperty == ABS!Spec

=============================================================================