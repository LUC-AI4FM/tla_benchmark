-------------------------------- MODULE ABCorrectness --------------------------------
EXTENDS Naturals

CONSTANT Data

VARIABLES sBit, sAck, rBit, sent, rcvd

cvars == << sBit, sAck, rBit, sent, rcvd >>

-----------------------------------------------------------------------------
TypeOK ==
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

-----------------------------------------------------------------------------
(* The sender sends a new value when its ack bit matches its send bit.     *)
CSndNewValue(d) ==
    /\ sAck = sBit
    /\ sent' = d
    /\ sBit' = 1 - sBit
    /\ UNCHANGED << sAck, rBit, rcvd >>

(* The receiver accepts a message when its bit differs from the sender bit.*)
CRcvMsg ==
    /\ rBit # sBit
    /\ rBit' = sBit
    /\ rcvd' = sent
    /\ UNCHANGED << sBit, sAck, sent >>

(* The sender accepts an ack when the receiver bit differs from sAck.      *)
CRcvAck ==
    /\ rBit # sAck
    /\ sAck' = rBit
    /\ UNCHANGED << sBit, rBit, sent, rcvd >>

ABCNext ==
    \/ \E d \in Data : CSndNewValue(d)
    \/ CRcvMsg
    \/ CRcvAck

-----------------------------------------------------------------------------
ABCFairness == WF_cvars(CRcvMsg) /\ WF_cvars(CRcvAck)

ABCSpec == ABCInit /\ [][ABCNext]_cvars /\ ABCFairness

Spec == ABCSpec

-----------------------------------------------------------------------------
(* Temporal property: sBit and sAck are infinitely often out of sync.      *)
InfinitelyOftenUnsynced == []<>(sAck # sBit)

THEOREM ABCSpec => []TypeOK
THEOREM ABCSpec => InfinitelyOftenUnsynced
=============================================================================