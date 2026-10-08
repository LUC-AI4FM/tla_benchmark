MODULE AsyncChannel
EXTENDS Naturals, TLC

CONSTANTS DataValues

VARIABLES ready, ack, data

Init ==
  /\ ready ∈ {0,1}
  /\ ack   ∈ {0,1}
  /\ ready = ack
  /\ data  ∈ DataValues

SenderTransmits ==
  /\ ready = ack
  /\ ∃ d ∈ DataValues :
       /\ ready' = 1 - ready
       /\ ack'   = ack
       /\ data'  = d

ReceiverConsumes ==
  /\ ready # ack
  /\ ready' = ready
  /\ ack'   = 1 - ack
  /\ data'  = data

Next == SenderTransmits \/ ReceiverConsumes

TypeInvariant ==
  /\ data ∈ DataValues
  /\ ready ∈ {0,1}
  /\ ack   ∈ {0,1}

Spec == Init /\ [][Next]_<<ready, ack, data>> /\ TypeInvariant

THEOREM Safe : Spec => []TypeInvariant