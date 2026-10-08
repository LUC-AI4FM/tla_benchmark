---------------------------- MODULE AltBit ----------------------------
EXTENDS Naturals, Sequences

CONSTANTS
    DATA \subseteq Nat

VARIABLES
    sBit, rBit, aBit, msg, recvMsg

vars == <<sBit, rBit, aBit, msg, recvMsg>>

TypeInvariant ==
  /\ sBit ∈ BOOLEAN
  /\ rBit ∈ BOOLEAN
  /\ aBit ∈ BOOLEAN
  /\ msg ∈ DATA
  /\ recvMsg ∈ DATA

Init ==
  /\ sBit = FALSE
  /\ rBit = TRUE
  /\ aBit = TRUE
  /\ msg = 0
  /\ recvMsg = 0

SenderSend ==
  /\ aBit = sBit
  /\ msg' = CHOOSE v ∈ DATA : TRUE
  /\ sBit' = NOT sBit
  /\ UNCHANGED <<rBit, aBit, recvMsg>>

ReceiverAccept ==
  /\ rBit # sBit
  /\ recvMsg' = msg
  /\ rBit' = NOT rBit
  /\ UNCHANGED <<sBit, aBit, msg>>

SenderAck ==
  /\ rBit # aBit
  /\ aBit' = rBit
  /\ UNCHANGED <<sBit, rBit, msg, recvMsg>>

Next == 
  \/ SenderSend
  \/ ReceiverAccept
  \/ SenderAck

Fairness ==
  WF_∅(ReceiverAccept) /\ WF_∅(SenderAck)

OutOfSync ==
  □◇ (sBit # aBit)

Spec ==
  Init /\ [][Next]_vars /\ TypeInvariant /\ Fairness /\ OutOfSync

=============================================================================