----------------------------- MODULE ABC -----------------------------
EXTENDS Naturals, TLC

CONSTANT Data

ASSUME Data /= {}

VARIABLES sBit, aBit, rBit, sVal, rVal

Bit == {0, 1}

vars == << sBit, aBit, rBit, sVal, rVal >>

Init ==
  /\ sBit \in Bit
  /\ aBit = sBit
  /\ rBit = sBit
  /\ sVal \in Data
  /\ rVal \in Data

SendNew ==
  /\ aBit = sBit
  /\ \E v \in Data:
       /\ sVal' = v
       /\ sBit' = 1 - sBit
  /\ UNCHANGED << aBit, rBit, rVal >>

RecvMsg ==
  /\ rBit # sBit
  /\ rVal' = sVal
  /\ rBit' = sBit
  /\ UNCHANGED << sBit, aBit, sVal >>

RecvAck ==
  /\ rBit # aBit
  /\ aBit' = rBit
  /\ UNCHANGED << sBit, rBit, sVal, rVal >>

Next == SendNew \/ RecvMsg \/ RecvAck

TypeInv ==
  /\ sBit \in Bit
  /\ aBit \in Bit
  /\ rBit \in Bit
  /\ sVal \in Data
  /\ rVal \in Data

InfinitelyOutOfSync == []<>(sBit # aBit)

ABCSpec ==
  Init
  /\ [][Next]_vars
  /\ WF_vars(RecvMsg)
  /\ WF_vars(RecvAck)
  /\ InfinitelyOutOfSync

=====================================================================