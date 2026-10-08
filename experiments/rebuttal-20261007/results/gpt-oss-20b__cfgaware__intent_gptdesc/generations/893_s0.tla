------------------------------ MODULE AsyncChannel ------------------------------
EXTENDS Naturals, TLC

CONSTANTS DataSet \* finite set of data items

VARIABLE val, ready, ack

(* Type invariant *)
TypeInvariant == /\ val \in DataSet
                 /\ ready \in BOOLEAN
                 /\ ack \in BOOLEAN

(* Initial state: channel holds a valid data element and readiness equals acknowledgement *)
Init == /\ val \in DataSet
        /\ ready = ack
        /\ ready \in BOOLEAN

(* Send action: can only occur when ready=ack; flips ready bit, stores new value *)
Send ==
  /\ ready = ack
  /\ val' \in DataSet
  /\ ready' = ~ready
  /\ ack' = ack

(* Receive action: can only occur when ready != ack; flips ack bit to match ready *)
Receive ==
  /\ ready /= ack
  /\ ready' = ready
  /\ ack' = ready
  /\ val' = val

Next == Send \/ Receive

Spec == Init /\ [][Next]_<<val,ready,ack>>

(* Invariants *)

HandshakeTransition == (ready' = ack') => Receive
ReliabilityNoOverwrite == (ready /= ack) => Receive
ReliabilityNoAckAbsent   == (ready = ack) => ~Receive

THEOREM TypeInvariantHolds ==
  Spec => []TypeInvariant

THEOREM HandshakeMaintained ==
  Spec => []HandshakeTransition

THEOREM NoOverwriteBeforeAck ==
  Spec => []ReliabilityNoOverwrite

THEOREM NoAckWhenAbsent ==
  Spec => []ReliabilityNoAckAbsent
=============================================================================