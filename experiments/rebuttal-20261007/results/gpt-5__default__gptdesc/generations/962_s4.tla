----------------------------- MODULE AlternatingBitProtocol -----------------------------

EXTENDS Naturals

CONSTANT Data

ASSUME Data /= {}

VARIABLES sBit, rBit, sAckBit, sVal, rVal

Bits == {0,1}

vars == << sBit, rBit, sAckBit, sVal, rVal >>

Init ==
  /\ sBit \in Bits
  /\ sAckBit = sBit
  /\ rBit = sBit
  /\ sVal \in Data
  /\ rVal \in Data

Send ==
  /\ sAckBit = sBit
  /\ \E d \in Data:
       /\ sVal' = d
       /\ sBit' = 1 - sBit
       /\ UNCHANGED << rBit, sAckBit, rVal >>

RcvMsg ==
  /\ rBit /= sBit
  /\ rVal' = sVal
  /\ rBit' = sBit
  /\ UNCHANGED << sBit, sAckBit, sVal >>

RcvAck ==
  /\ rBit /= sAckBit
  /\ sAckBit' = rBit
  /\ UNCHANGED << sBit, rBit, sVal, rVal >>

Next == Send \/ RcvMsg \/ RcvAck

TypeInv ==
  /\ sBit \in Bits
  /\ rBit \in Bits
  /\ sAckBit \in Bits
  /\ sVal \in Data
  /\ rVal \in Data

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(RcvMsg)
  /\ WF_vars(RcvAck)

OutOfSync == []<>(sBit /= sAckBit)

========================================================================================