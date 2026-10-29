---------------------------- MODULE MC_Session11b ----------------------------
EXTENDS Session11b, Sequences, Naturals, FiniteSets, TLC

(***************************************************************************)
(* Model-checking wrapper for the alternating bit protocol specification  *)
(* in Session11b. Session11a (the high-level ABSpec) is instantiated so   *)
(* that its Spec can be checked as a property of the lower-level spec.    *)
(***************************************************************************)

CONSTANTS d1, d2, d3

\* Concrete finite message set, substituted for Data in the model
ConstData == {d1, d2, d3}

\* State constraint that bounds the lengths of the two channels
SeqConstraint == /\ Len(AtoB) \leq 3
                 /\ Len(BtoA) \leq 3

\* Type correctness of the communication state
AB_TypeOK == /\ AVar \in Data \X {0, 1}
             /\ BVar \in Data \X {0, 1}
             /\ AtoB \in Seq(Data \X {0, 1})
             /\ BtoA \in Seq({0, 1})

\* Simple invariant over the communication state
AB_Inv ==
  /\ AB_TypeOK
  /\ (AVar[2] = BVar[2]) => (AVar = BVar)
  /\ \A i \in 1..Len(AtoB) : (AtoB[i][2] = AVar[2]) => (AtoB[i] = AVar)

\* Helper operators for AB_TwoValsSeq
AB_Reverse(s) == [i \in 1..Len(s) |-> s[Len(s) - i + 1]]

AB_Bits(s) == [i \in 1..Len(s) |-> s[i][2]]

\* True iff the sequence s changes value at most once
AB_IsTwoValsSeq(s) ==
  Cardinality({i \in 1..(Len(s) - 1) : s[i] # s[i + 1]}) \leq 1

\* The bits, read in order along the message path
\* A -> AtoB -> B -> BtoA, consist of at most two blocks of equal values.
AB_BitSeq == <<AVar[2]>> \o AB_Reverse(AB_Bits(AtoB))
               \o <<BVar[2]>> \o AB_Reverse(BtoA)

AB_TwoValsSeq == AB_IsTwoValsSeq(AB_BitSeq)

\* Instance of the high-level specification from Session11a
ABS == INSTANCE Session11a

\* The property that the Session11b spec implements the Session11a spec
ABSpecProperty == ABS!Spec

=============================================================================