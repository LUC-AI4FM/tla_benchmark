------------------------------- MODULE AB2 -------------------------------
(***************************************************************************)
(* Alternating Bit Protocol: data refinement verification.                 *)
(*                                                                         *)
(* The concrete implementation (AB2) represents a message as a tuple       *)
(* <<d, b>>. The abstract specification (ABSpec) represents a message as   *)
(* a record [data |-> d, bit |-> b]. A refinement mapping translates the   *)
(* concrete state into the abstract state. ABSpecProperty is the abstract  *)
(* specification written over the mapped state, so TLC can check that      *)
(* Spec => ABSpecProperty.                                                 *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANT Data

ConstData == {"a", "b", "c"}

VARIABLES sAB,   \* sender state:   <<data, bit>>
          rAB,   \* receiver state: <<data, bit>>
          msgQ,  \* channel sender -> receiver: sequence of <<data, bit>>
          ackQ   \* channel receiver -> sender: sequence of bits

vars == <<sAB, rAB, msgQ, ackQ>>

Msgs == Data \X {0, 1}

Remove(i, seq) ==
  [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]

-----------------------------------------------------------------------------
(*************************** Implementation (tuples) ***********************)

AB2_TypeOK ==
  /\ sAB \in Msgs
  /\ rAB \in Msgs
  /\ msgQ \in Seq(Msgs)
  /\ ackQ \in Seq({0, 1})

Init ==
  /\ \E d \in Data : sAB = <<d, 1>>
  /\ rAB = sAB
  /\ msgQ = << >>
  /\ ackQ = << >>

SndMsg ==
  /\ msgQ' = Append(msgQ, sAB)
  /\ UNCHANGED <<sAB, rAB, ackQ>>

RcvAck ==
  /\ ackQ # << >>
  /\ IF Head(ackQ) = sAB[2]
       THEN \E d \in Data : sAB' = <<d, 1 - sAB[2]>>
       ELSE UNCHANGED sAB
  /\ ackQ' = Tail(ackQ)
  /\ UNCHANGED <<rAB, msgQ>>

SndAck ==
  /\ ackQ' = Append(ackQ, rAB[2])
  /\ UNCHANGED <<sAB, rAB, msgQ>>

RcvMsg ==
  /\ msgQ # << >>
  /\ IF Head(msgQ)[2] # rAB[2]
       THEN rAB' = Head(msgQ)
       ELSE UNCHANGED rAB
  /\ msgQ' = Tail(msgQ)
  /\ UNCHANGED <<sAB, ackQ>>

LoseMsg ==
  \/ /\ \E i \in 1..Len(msgQ) : msgQ' = Remove(i, msgQ)
     /\ UNCHANGED <<sAB, rAB, ackQ>>
  \/ /\ \E i \in 1..Len(ackQ) : ackQ' = Remove(i, ackQ)
     /\ UNCHANGED <<sAB, rAB, msgQ>>

Next == SndMsg \/ RcvAck \/ SndAck \/ RcvMsg \/ LoseMsg

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ SF_vars(RcvAck)
  /\ SF_vars(RcvMsg)
  /\ WF_vars(SndMsg)
  /\ WF_vars(SndAck)

StateConstraint == Len(msgQ) <= 3 /\ Len(ackQ) <= 3

-----------------------------------------------------------------------------
(************************* Refinement mapping (records) ********************)

TupleToRec(t) == [data |-> t[1], bit |-> t[2]]

mAVar == TupleToRec(sAB)
mBVar == TupleToRec(rAB)
mAtoB == [i \in 1..Len(msgQ) |-> TupleToRec(msgQ[i])]
mBtoA == ackQ

mvars == <<mAVar, mBVar, mAtoB, mBtoA>>

-----------------------------------------------------------------------------
(********************* Abstract specification (ABSpec) *********************)
(* Written over the mapped state expressions.                              *)

ARecMsgs == [data : Data, bit : {0, 1}]

A_TypeOK ==
  /\ mAVar \in ARecMsgs
  /\ mBVar \in ARecMsgs
  /\ mAtoB \in Seq(ARecMsgs)
  /\ mBtoA \in Seq({0, 1})

A_Init ==
  /\ mAVar \in [data : Data, bit : {1}]
  /\ mBVar = mAVar
  /\ mAtoB = << >>
  /\ mBtoA = << >>

A_ASnd ==
  /\ mAtoB' = Append(mAtoB, mAVar)
  /\ UNCHANGED <<mAVar, mBVar, mBtoA>>

A_ARcv ==
  /\ mBtoA # << >>
  /\ IF Head(mBtoA) = mAVar.bit
       THEN \E d \in Data : mAVar' = [data |-> d, bit |-> 1 - mAVar.bit]
       ELSE UNCHANGED mAVar
  /\ mBtoA' = Tail(mBtoA)
  /\ UNCHANGED <<mBVar, mAtoB>>

A_BSnd ==
  /\ mBtoA' = Append(mBtoA, mBVar.bit)
  /\ UNCHANGED <<mAVar, mBVar, mAtoB>>

A_BRcv ==
  /\ mAtoB # << >>
  /\ IF Head(mAtoB).bit # mBVar.bit
       THEN mBVar' = Head(mAtoB)
       ELSE UNCHANGED mBVar
  /\ mAtoB' = Tail(mAtoB)
  /\ UNCHANGED <<mAVar, mBtoA>>

A_LoseMsg ==
  \/ /\ \E i \in 1..Len(mAtoB) : mAtoB' = Remove(i, mAtoB)
     /\ UNCHANGED <<mAVar, mBVar, mBtoA>>
  \/ /\ \E i \in 1..Len(mBtoA) : mBtoA' = Remove(i, mBtoA)
     /\ UNCHANGED <<mAVar, mBVar, mAtoB>>

A_Next == A_ASnd \/ A_ARcv \/ A_BSnd \/ A_BRcv \/ A_LoseMsg

ABSpecProperty ==
  /\ A_Init
  /\ [][A_Next]_mvars
  /\ SF_mvars(A_ARcv)
  /\ SF_mvars(A_BRcv)
  /\ WF_mvars(A_ASnd)
  /\ WF_mvars(A_BSnd)

=============================================================================