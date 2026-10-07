----------------------------- MODULE AlternatingBitProtocol -----------------------------

EXTENDS Naturals

CONSTANT Data

ASSUME Data # {}

VARIABLES sBit, aBit, rBit, sData, rData

vars == << sBit, aBit, rBit, sData, rData >>

Bits == {0, 1}

TypeOK ==
  /\ sBit \in Bits
  /\ aBit \in Bits
  /\ rBit \in Bits
  /\ sData \in Data
  /\ rData \in Data

Init ==
  /\ TypeOK
  /\ sBit = aBit
  /\ aBit = rBit

SendNew ==
  /\ aBit = sBit
  /\ sBit' = 1 - sBit
  /\ sData' \in Data
  /\ UNCHANGED << aBit, rBit, rData >>

ReceiveMsg ==
  /\ rBit # sBit
  /\ rBit' = sBit
  /\ rData' = sData
  /\ UNCHANGED << sBit, aBit, sData >>

ReceiveAck ==
  /\ rBit # aBit
  /\ aBit' = rBit
  /\ UNCHANGED << sBit, rBit, sData, rData >>

Next == SendNew \/ ReceiveMsg \/ ReceiveAck

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(ReceiveMsg)
  /\ WF_vars(ReceiveAck)

TypeInvariant == TypeOK

InfinitelyOftenOutOfSync == []<>(sBit # aBit)

========================================================================================