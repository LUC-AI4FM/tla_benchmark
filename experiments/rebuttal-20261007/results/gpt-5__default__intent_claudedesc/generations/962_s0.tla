----------------------------- MODULE ABP -----------------------------
EXTENDS Naturals

CONSTANT Data

VARIABLES sData, sBit, rData, rBit, ackBit

Bits == {0, 1}

vars == << sData, sBit, rData, rBit, ackBit >>

Init ==
  /\ sData \in Data
  /\ rData \in Data
  /\ sBit \in Bits
  /\ rBit \in Bits
  /\ ackBit \in Bits
  /\ sBit = rBit
  /\ ackBit = sBit

Send ==
  /\ ackBit = sBit
  /\ \E d \in Data:
       /\ sData' = d
       /\ sBit' = 1 - sBit
       /\ rData' = rData
       /\ rBit' = rBit
       /\ ackBit' = ackBit

Receive ==
  /\ rBit # sBit
  /\ rData' = sData
  /\ rBit' = sBit
  /\ sData' = sData
  /\ sBit' = sBit
  /\ ackBit' = ackBit

Acknowledge ==
  /\ ackBit # rBit
  /\ ackBit' = rBit
  /\ sData' = sData
  /\ sBit' = sBit
  /\ rData' = rData
  /\ rBit' = rBit

Next == Send \/ Receive \/ Acknowledge

TypeInv ==
  /\ sData \in Data
  /\ rData \in Data
  /\ sBit \in Bits
  /\ rBit \in Bits
  /\ ackBit \in Bits

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Receive)
  /\ WF_vars(Acknowledge)
============================================================================