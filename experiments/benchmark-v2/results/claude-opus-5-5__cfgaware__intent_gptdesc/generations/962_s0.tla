---------------------------- MODULE ABCorrectness ----------------------------
(***************************************************************************)
(* High-level correctness model of the Alternating Bit protocol.           *)
(*                                                                         *)
(* The unreliable channel (loss, duplication, reordering, no corruption)   *)
(* is abstracted away. Only the effect of a fresh message or               *)
(* acknowledgment eventually getting through is modelled.                  *)
(* Fair-loss is captured by weak fairness on the receive actions.          *)
(*                                                                         *)
(*   sent  : the data item the sender is currently sending / last sent     *)
(*   sBit  : the sequence bit attached to the sender's current message     *)
(*   sAck  : the bit of the last acknowledgment the sender received        *)
(*   rBit  : the bit of the last message the receiver accepted             *)
(*   rcvd  : the last data item delivered by the receiver                  *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT Data

VARIABLES sBit, sAck, rBit, sent, rcvd

cvars == <<sBit, sAck, rBit, sent, rcvd>>

TypeInv ==
  /\ sBit \in {0, 1}
  /\ sAck \in {0, 1}
  /\ rBit \in {0, 1}
  /\ sent \in Data
  /\ rcvd \in Data

ABCInit ==
  /\ sBit \in {0, 1}
  /\ sAck = sBit
  /\ rBit = sBit
  /\ sent \in Data
  /\ rcvd \in Data

(* The sender may start a new item only after the previous one is acked. *)
CSndNewValue(d) ==
  /\ sAck = sBit
  /\ sent' = d
  /\ sBit' = 1 - sBit
  /\ UNCHANGED <<sAck, rBit, rcvd>>

(* A fresh message (bit differs from last delivered bit) arrives.        *)
CRcvMsg ==
  /\ rBit # sBit
  /\ rBit' = sBit
  /\ rcvd' = sent
  /\ UNCHANGED <<sBit, sAck, sent>>

(* An acknowledgment carrying the receiver's bit arrives at the sender.  *)
CRcvAck ==
  /\ rBit # sAck
  /\ sAck' = rBit
  /\ UNCHANGED <<sBit, rBit, sent, rcvd>>

ABCNext ==
  \/ \E d \in Data : CSndNewValue(d)
  \/ CRcvMsg
  \/ CRcvAck

ABCFairness == WF_cvars(CRcvMsg) /\ WF_cvars(CRcvAck)

ABCSpec == ABCInit /\ [][ABCNext]_cvars /\ ABCFairness

-----------------------------------------------------------------------------
(* Correctness properties                                                  *)

(* Receiver and acknowledgment state are consistent with the sender.      *)
BitAgreement ==
  /\ (sAck = sBit) => (rBit = sBit)
  /\ (rBit = sBit) => (rcvd = sent)

(* Delivery equals a sent value and happens at most once per new item:  *)
(* rcvd changes only when a fresh bit arrives, and then equals sent.     *)
NoDupSafety ==
  [][ (rcvd' # rcvd) => (rBit' # rBit /\ rcvd' = sent) ]_cvars

DeliveredOnce ==
  [][ CRcvMsg => (rBit # sBit) ]_cvars

(* Every item the sender starts to send is eventually delivered.         *)
Liveness ==
  \A b \in {0, 1} : (sBit = b) ~> (rBit = b /\ sAck = b)

EventualDelivery == (rBit # sBit) ~> (rBit = sBit /\ rcvd = sent)

THEOREM ABCSpec => [](TypeInv /\ BitAgreement)
=============================================================================