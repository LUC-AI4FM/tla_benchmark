------------------------------ MODULE ABCorrectness ------------------------------
EXTENDS Integers

CONSTANTS Data

VARS sBit, sAck, rBit, sent, rcvd

(* --- Initialization ----------------------------------------------------- *)
Init == /\ sBit \in {0,1}
      /\ sAck \in {0,1}
      /\ rBit \in {0,1}
      /\ sent  \in Data
      /\ rcvd  \in Data
      /\ sBit = sAck
      /\ sBit = rBit

(* --- Actions ------------------------------------------------------------ *)
CSndNewValue == /\ sAck = sBit
               /\ sent'   \in Data
               /\ sBit'   = 1 - sBit
               /\ UNCHANGED <<sAck, rBit, rcvd>>

CRcvMsg == /\ rBit # sBit
           /\ rBit'   = sBit
           /\ rcvd'   = sent
           /\ UNCHANGED <<sBit, sAck>>

CRcvAck == /\ sAck # rBit
           /\ sAck'   = rBit
           /\ UNCHANGED <<sBit, sent, rcvd>>

Stutter == /\ UNCHANGED <<sBit, sAck, rBit, sent, rcvd>>

Next == CSndNewValue \/ CRcvMsg \/ CRcvAck \/ Stutter

(* --- Specification ----------------------------------------------------- *)
ABCSpec == Init
          /\ [][Next]_vars
          /\ WF_vars(CRcvMsg)
          /\ WF_vars(CRcvAck)

(* --- Type Invariant ---------------------------------------------------- *)
TypeInv == /\ sBit \in {0,1}
           /\ sAck  \in {0,1}
           /\ rBit  \in {0,1}
           /\ sent  \in Data
           /\ rcvd  \in Data

THEOREM TypeInvariantHolds == ABCSpec => []TypeInv
=============================================================================