------------------------------- MODULE MCAB -------------------------------
(***************************************************************************)
(* Model-checking wrapper for the Alternating Bit protocol specification   *)
(* defined in module Session11b.  Module Session11a, the high-level        *)
(* specification, is instantiated so its Spec can be checked as a          *)
(* property of the protocol.                                               *)
(***************************************************************************)
EXTENDS Session11b, Integers, Sequences, TLC

(***************************************************************************)
(* A concrete finite set of messages, used to override constant Data.      *)
(***************************************************************************)
CONSTANTS d1, d2, d3

ConstData == {d1, d2, d3}

(***************************************************************************)
(* State constraint bounding the length of the two channels so that the    *)
(* reachable state space is finite.                                        *)
(***************************************************************************)
SeqConstraint == /\ Len(AtoB) \leq 3
                 /\ Len(BtoA) \leq 3

(***************************************************************************)
(* Type correctness of the communication state.                            *)
(***************************************************************************)
AB_TypeOK == /\ AVar \in Data \X {0, 1}
             /\ BVar \in Data \X {0, 1}
             /\ AtoB \in Seq(Data \X {0, 1})
             /\ BtoA \in Seq({0, 1})

(***************************************************************************)
(* A simple inductive-style invariant.                                     *)
(***************************************************************************)
AB_Inv ==
  /\ AB_TypeOK
  /\ (AVar[2] = BVar[2]) => (AVar = BVar)
  /\ \A i \in 1..Len(AtoB) : AtoB[i] \in {AVar, BVar}
  /\ \A i \in 1..Len(BtoA) : BtoA[i] \in {AVar[2], BVar[2]}

(***************************************************************************)
(* TwoValsSeq(s) is true iff s has the form <<v1,...,v1,v2,...,v2>>, that   *)
(* is, it contains at most two distinct values, each forming one           *)
(* contiguous block.                                                       *)
(***************************************************************************)
TwoValsSeq(s) ==
  \E k \in 0..Len(s) :
     /\ \A i \in 1..k : s[i] = s[1]
     /\ \A i \in (k+1)..Len(s) : s[i] = s[Len(s)]

AB_TwoValsSeq == /\ TwoValsSeq(AtoB)
                 /\ TwoValsSeq(BtoA)

(***************************************************************************)
(* The high-level specification, used as a property to check.              *)
(***************************************************************************)
ABS == INSTANCE Session11a

ABSpecProperty == ABS!Spec
=============================================================================