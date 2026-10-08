------------------------------ MODULE Handshake ------------------------------
EXTENDS Naturals

CONSTANTS DataSet

VARIABLES ready, ack, data

(* Type safety *)
TypeSafe == 
  /\ ready ∈ BOOLEAN
  /\ ack ∈ BOOLEAN
  /\ data ∈ DataSet

Init == 
  /\ ready = FALSE
  /\ ack = FALSE
  /\ data ∈ DataSet
  /\ TypeSafe

SenderAction ==
  /\ ready = ack
  /\ \E d \in DataSet : 
        /\ data' = d
        /\ ready' = ~ready
        /\ ack' = ack

ReceiverAction ==
  /\ ready # ack
  /\ ready' = ready
  /\ ack' = ~ack
  /\ data' = data

Next == SenderAction \/ ReceiverAction

Spec == Init /\ [][Next]_vars /\ WF_action(SenderAction) /\ WF_action(ReceiverAction) /\ []TypeSafe

=============================================================================